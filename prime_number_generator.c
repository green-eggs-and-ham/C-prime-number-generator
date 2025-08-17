/*
* A multi-threaded prime number generator using cache optimised 
* sieve of Eratosthenes by Oscar Bullen (13-06-2025)
*/

#include <ctype.h>
#include <errno.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <windows.h>
#include <math.h>
#include <time.h>
#include <sysinfoapi.h>

#define RESOLUTION 3
#define TEMP_FILE_PATTERN "prime_tmp_%d_%d.txt"
#define MAX_FILENAME_LENGTH 256
#define INPUT_BUFFER_SIZE 256
#define FILE_BUFFER_SIZE (1024 * 1024)
#define IN_MEMORY_THRESHOLD (1ULL << 30) 
#define BENCHMARK_RUNS 3
#define MAX_THREADS 128
#define MEMORY_LOCK_LIMIT (10 * 1024 * 1024) /* 10MB */

/* Structure for storing base primes */
typedef struct {
    uint32_t *primes;
    uint64_t count;
} BasePrimes;

/* Benchmark results structure */
typedef struct {
    double count_time;
    double text_time;
    double bitarray_time;
    uint64_t prime_count;
    int num_threads;
    double count_thread_times[MAX_THREADS];
} BenchmarkResults;

/* Utility Functions */

/**
 * Detect L1 cache size using PowerShell command
 * Falls back to 32KB if detection fails
 */
static uint64_t get_l1_cache_size() {
    FILE *fp = _popen(
        "powershell -Command \"Get-WmiObject Win32_CacheMemory | "
        "Sort-Object Level | Select-Object -First 1 -ExpandProperty MaxCacheSize\"", 
        "r"
    );

    if (fp == NULL) {
        fprintf(stderr, "Warning: Failed to detect L1 cache size. Using 32KB default.\n");
        return 32 * 1024;  /* Fallback value */
    }

    char buffer[128];
    uint64_t cache_size_kb = 0;
    
    if (fgets(buffer, sizeof(buffer), fp) != NULL) {
        cache_size_kb = strtoull(buffer, NULL, 10);
    }
    
    _pclose(fp);

    /* Validate detected cache size */
    if (cache_size_kb < 8 || cache_size_kb > 16384) {
        fprintf(stderr, "Warning: Detected cache size %llu KB is invalid. Using 32KB default.\n", cache_size_kb);
        return 32 * 1024;
    }

    return cache_size_kb * 1024;
}

/**
* Returns currently free memory or a fallback value
*/
static uint64_t get_available_physical_memory() {
    MEMORYSTATUSEX memStatus;
    memStatus.dwLength = sizeof(memStatus);
    if (!GlobalMemoryStatusEx(&memStatus)) {
        fprintf(stderr, "Warning: GlobalMemoryStatusEx failed (error %lu). Using conservative estimate.\n", GetLastError());
        return 1 * 1024 * 1024 * 1024; /* 1GB fallback */
    }
    return memStatus.ullAvailPhys;
}

/**
 * Lock memory region if within size limits
 */
static bool lock_memory(void* addr, size_t size) {
    if (size <= MEMORY_LOCK_LIMIT) {
        if (!VirtualLock(addr, size)) {
            DWORD err = GetLastError();
            if (err != ERROR_NO_SYSTEM_RESOURCES) { /* Suppress specific warning */
                fprintf(stderr, "Warning: VirtualLock failed (error %lu). Size: %zu bytes\n", 
                        err, size);
            }
            return false;
        }
        return true;
    }
    return false;
}

/**
 * Unlock memory region if previously locked
 */
static void unlock_memory(void* addr, size_t size) {
    if (size <= MEMORY_LOCK_LIMIT) {
        VirtualUnlock(addr, size);
    }
}

/**
 * Pre-fault and lock base primes in memory
 */
static void optimize_base_primes(BasePrimes bp, const SYSTEM_INFO* sysinfo) {
    if (bp.primes && bp.count > 0) {
        size_t total_size = bp.count * sizeof(uint32_t);
        
        /* Pre-fault all pages */
        const int page_size = sysinfo->dwPageSize;
        for (size_t i = 0; i < total_size; i += page_size) {
            bp.primes[i / sizeof(uint32_t)] = bp.primes[i / sizeof(uint32_t)];
        }
        
        /* Lock memory */
        lock_memory(bp.primes, total_size);
    }
}

/**
 * Generate base primes using Sieve of Eratosthenes
 * Returns BasePrimes structure containing primes up to limit
 */
static BasePrimes generate_base_primes(uint64_t limit) {
    BasePrimes bp = { NULL, 0 };
    
    if (limit < 2) {
        return bp;
    }

    const uint64_t num_odds = (limit + 1) / 2;
    const size_t num_bytes = (num_odds + 7) / 8;
    unsigned char *sieve = (unsigned char*)calloc(num_bytes, 1);
    
    if (!sieve) {
        fprintf(stderr, "Error: Failed to allocate %zu bytes for base sieve\n", num_bytes);
        exit(EXIT_FAILURE);
    }

    /* Mark 1 as not prime (since we only store odd numbers) */
    sieve[0] |= 1;

    const uint64_t sqrt_limit = (uint64_t)sqrt((double)limit) + 1;
    
    /* Sieve odd numbers */
    for (uint64_t i = 1; i < num_odds; i++) {
        const uint64_t p = 2 * i + 1;
        if (p > sqrt_limit) break;
        if (sieve[i >> 3] & (1 << (i & 7))) continue;

        /* Mark multiples of p starting from p^2 */
        const uint64_t start_index = (p * p) / 2;
        for (uint64_t j = start_index; j < num_odds; j += p) {
            sieve[j >> 3] |= (1 << (j & 7));
        }
    }

    /* Count primes (including 2) */
    uint64_t count = 1;
    for (uint64_t i = 1; i < num_odds; i++) {
        if (!(sieve[i >> 3] & (1 << (i & 7)))) {
            count++;
        }
    }

    uint32_t *primes = (uint32_t*)malloc(count * sizeof(uint32_t));
    if (!primes) {
        fprintf(stderr, "Error: Failed to allocate %llu bytes for base primes\n", count * sizeof(uint32_t));
        free(sieve);
        exit(EXIT_FAILURE);
    }

    primes[0] = 2;
    uint64_t index = 1;
    
    for (uint64_t i = 1; i < num_odds; i++) {
        if (!(sieve[i >> 3] & (1 << (i & 7)))) {
            primes[index++] = (uint32_t)(2 * i + 1);
        }
    }

    free(sieve);
    bp.primes = primes;
    bp.count = count;
    return bp;
}

/**
 * Safely read and validate user input
 * Returns true if valid uint64_t obtained
 */
static bool get_input(uint64_t *value) {
    char buffer[INPUT_BUFFER_SIZE];
    if (fgets(buffer, sizeof(buffer), stdin) == NULL) {
        printf("Error: unable to read input.\n");
        return false;
    }
    
    /* Trim trailing whitespace */
    size_t len = strlen(buffer);
    while (len > 0 && isspace((unsigned char)buffer[len - 1])) {
        buffer[--len] = '\0';
    }
    
    /* Skip leading whitespace */
    char *start = buffer;
    while (isspace((unsigned char)*start)) {
        start++;
    }
    
    /* Check for empty input */
    if (*start == '\0') {
        printf("Error: input is empty.\n");
        return false;
    }
    
    /* Validate input format */
    if (*start == '+' || *start == '-') {
        printf("Error: input cannot have sign character.\n");
        return false;
    }
    
    for (char *p = start; *p != '\0'; p++) {
        if (!isdigit((unsigned char)*p)) {
            printf("Error: input must be a positive integer.\n");
            return false;
        }
    }
    
    /* Check length */
    const size_t num_len = strlen(start);
    if (num_len > 20) {
        printf("Error: maximum input size exceeded (20 digits).\n");
        return false;
    }
    
    /* Convert to uint64_t */
    char *endptr;
    errno = 0;
    const unsigned long long temp = strtoull(start, &endptr, 10);
    
    if (*endptr != '\0') {
        printf("Error: invalid characters in input.\n");
        return false;
    }
    
    if (errno == ERANGE || temp > UINT64_MAX) {
        printf("Error: input exceeds maximum value (18446744073709551615).\n");
        return false;
    }
    
    *value = (uint64_t)temp;
    return true;
}

/* Sieve Functions */

/**
 * Count primes up to N using segmented sieve
 */
static uint64_t sieve_count(uint64_t N, uint64_t cache_size, bool silent, double *thread_times) {
    const uint64_t sqrtN = (uint64_t)ceil(sqrt((double)N));
    const uint64_t segment_bytes = cache_size;
    const uint64_t segment_bits = segment_bytes * 8;
    const uint64_t segment_count = (N + 2 * segment_bits - 1) / (2 * segment_bits);

    BasePrimes bp = generate_base_primes(sqrtN);
    uint32_t *base_primes = bp.primes;
    const uint64_t base_primes_count = bp.count;

    /* Get system information */
    SYSTEM_INFO sysinfo;
    GetSystemInfo(&sysinfo);
    const int num_threads = sysinfo.dwNumberOfProcessors;
    optimize_base_primes(bp, &sysinfo);

    const uint64_t segments_per_thread = (segment_count + num_threads - 1) / num_threads;

    /* Structure for thread data */
    typedef struct {
        uint64_t start_seg;
        uint64_t end_seg;
        uint64_t count;
        double time_taken;
        uint64_t *next_multiples;
    } ThreadData;

    /* Allocate thread data */
    ThreadData *thread_data = calloc(num_threads, sizeof(ThreadData));
    HANDLE *threads = malloc(num_threads * sizeof(HANDLE));
    if (!thread_data || !threads) {
        fprintf(stderr, "Error: Failed to allocate thread structures\n");
        exit(EXIT_FAILURE);
    }

    /* Initialize thread data */
    for (int i = 0; i < num_threads; i++) {
        thread_data[i].start_seg = i * segments_per_thread;
        thread_data[i].end_seg = (i + 1) * segments_per_thread;
        if (thread_data[i].end_seg > segment_count) {
            thread_data[i].end_seg = segment_count;
        }
        
        thread_data[i].next_multiples = malloc(base_primes_count * sizeof(uint64_t));
        if (!thread_data[i].next_multiples) {
            fprintf(stderr, "Error: Failed to allocate next_multiples array\n");
            exit(EXIT_FAILURE);
        }
        
        /* Initialize next multiples */
        for (uint64_t k = 0; k < base_primes_count; k++) {
            const uint32_t p = base_primes[k];
            thread_data[i].next_multiples[k] = (p >= 3) ? (uint64_t)p * p : 0;
        }
    }

    /* Define thread function for counting */
    DWORD WINAPI sieve_segment(LPVOID param) {
        ThreadData *data = (ThreadData*)param;
        data->count = 0;
        data->time_taken = 0.0;
        
        /* Get thread times at start */
        FILETIME createTime, exitTime, kernelTimeStart, userTimeStart;
        if (!GetThreadTimes(GetCurrentThread(), &createTime, &exitTime, &kernelTimeStart, &userTimeStart)) {
            fprintf(stderr, "Warning: GetThreadTimes failed (error %lu)\n", GetLastError());
        }
        
        const uint64_t segment_bytes = cache_size;
        const uint64_t segment_bits = segment_bytes * 8;

        for (uint64_t seg_index = data->start_seg; seg_index < data->end_seg; seg_index++) {
            const uint64_t low = seg_index * (2 * segment_bits);
            uint64_t high = low + 2 * segment_bits - 1;
            if (low > N) break;
            if (high > N) high = N;

            unsigned char *segment = calloc(segment_bytes, 1);
            if (!segment) {
                fprintf(stderr, "Error: Failed to allocate segment memory\n");
                exit(EXIT_FAILURE);
            }

            /* Sieve the segment */
            for (uint64_t k = 0; k < base_primes_count; k++) {
                const uint32_t p = base_primes[k];
                if (p < 3) continue;

                uint64_t next = data->next_multiples[k];
                if (next > high) continue;

                /* Adjust starting point if needed */
                if (next < low) {
                    const uint64_t remainder = low % p;
                    uint64_t start = low - remainder;
                    if (remainder > 0) start += p;
                    if (start % 2 == 0) start += p;
                    next = start;
                }

                /* Mark multiples in current segment */
                const uint64_t start_j = (next - (low + 1)) / 2;
                const uint64_t step = p;
                const uint64_t limit = (high - (low + 1)) / 2;
                
                for (uint64_t j = start_j; j <= limit; j += step) {
                    segment[j >> 3] |= (1 << (j & 7));
                }
                
                data->next_multiples[k] = next + step * ((limit - start_j) / step + 1) * 2;
            }

            /* Count primes in this segment */
            uint64_t count_segment = 0;
            for (uint64_t j = 0; j < segment_bits; j++) {
                const uint64_t num = low + 1 + 2 * j;
                if (num > N || num < 3) continue;
                if (!(segment[j >> 3] & (1 << (j & 7)))) {
                    count_segment++;
                }
            }

            data->count += count_segment;
            free(segment);
        }
        

        FILETIME kernelTimeEnd, userTimeEnd;
        if (!GetThreadTimes(GetCurrentThread(), &createTime, &exitTime, &kernelTimeEnd, &userTimeEnd)) {
            fprintf(stderr, "Warning: GetThreadTimes failed (error %lu)\n", GetLastError());
            return 0;
        }
        
        /* Calculate CPU time for this thread */
        ULARGE_INTEGER userStart, userEnd, kernelStart, kernelEnd;
        userStart.LowPart = userTimeStart.dwLowDateTime;
        userStart.HighPart = userTimeStart.dwHighDateTime;
        userEnd.LowPart = userTimeEnd.dwLowDateTime;
        userEnd.HighPart = userTimeEnd.dwHighDateTime;
        
        kernelStart.LowPart = kernelTimeStart.dwLowDateTime;
        kernelStart.HighPart = kernelTimeStart.dwHighDateTime;
        kernelEnd.LowPart = kernelTimeEnd.dwLowDateTime;
        kernelEnd.HighPart = kernelTimeEnd.dwHighDateTime;
        
        double userTime = (userEnd.QuadPart - userStart.QuadPart) * 1e-7;
        double kernelTime = (kernelEnd.QuadPart - kernelStart.QuadPart) * 1e-7;
        data->time_taken = userTime + kernelTime;
        
        return 0;
    }

    /* Create threads */
    for (int i = 0; i < num_threads; i++) {
        threads[i] = CreateThread(NULL, 0, sieve_segment, &thread_data[i], 0, NULL);
        if (!threads[i]) {
            fprintf(stderr, "Error: Failed to create thread\n");
            exit(EXIT_FAILURE);
        }
    }

    /* Wait for threads to complete */
    WaitForMultipleObjects(num_threads, threads, TRUE, INFINITE);

    /* Aggregate results */
    uint64_t total_count = 1;  /* Include 2 */
    for (int i = 0; i < num_threads; i++) {
        total_count += thread_data[i].count;
        if (thread_times) {
            thread_times[i] = thread_data[i].time_taken;
        }
        free(thread_data[i].next_multiples);
        CloseHandle(threads[i]);
    }

    /* Clean up */
    free(threads);
    free(thread_data);
    unlock_memory(base_primes, base_primes_count * sizeof(uint32_t));
    free(base_primes);

    if (!silent) {
        printf("Number of primes up to %llu: %llu\n", N, total_count);
    }
    return total_count;
}

/**
 * Estimate text file size for primes list
 */
static uint64_t estimate_text_file_size(uint64_t N, uint64_t prime_count) {
    /* Estimate average digits per prime: log10(N) + 1 (for the largest prime) */
    double avg_digits = log10((double)N) + 1;
    /* Add 1 character for newline */
    double bytes_per_prime = avg_digits + 1;
    
    /* Calculate estimated size */
    uint64_t estimated_size = (uint64_t)(prime_count * bytes_per_prime);
    
    /* Add 3 bytes for "2\n" at the start */
    return estimated_size + 3;
}

/**
 * Generate primes list and save to text file
 */
static uint64_t sieve_text(uint64_t N, const char *filename, uint64_t cache_size, bool silent) {
    const uint64_t sqrtN = (uint64_t)ceil(sqrt((double)N));
    const uint64_t segment_bytes = cache_size;
    const uint64_t segment_bits = segment_bytes * 8;
    const uint64_t segment_count = (N + 2 * segment_bits - 1) / (2 * segment_bits);

    BasePrimes bp = generate_base_primes(sqrtN);
    uint32_t *base_primes = bp.primes;
    const uint64_t base_primes_count = bp.count;

    SYSTEM_INFO sysinfo;
    GetSystemInfo(&sysinfo);
    const int num_threads = sysinfo.dwNumberOfProcessors;
    optimize_base_primes(bp, &sysinfo);

    const uint64_t segments_per_thread = (segment_count + num_threads - 1) / num_threads;

    typedef struct {
        uint64_t start_seg;
        uint64_t end_seg;
        uint64_t count;
        uint64_t *next_multiples;
        FILE *outfile;
        char tmp_filename[MAX_PATH];
    } ThreadData;

    ThreadData *thread_data = calloc(num_threads, sizeof(ThreadData));
    HANDLE *threads = malloc(num_threads * sizeof(HANDLE));
    if (!thread_data || !threads) {
        fprintf(stderr, "Error: Failed to allocate thread structures\n");
        exit(EXIT_FAILURE);
    }

    const int pid = GetCurrentProcessId();
    for (int i = 0; i < num_threads; i++) {
        thread_data[i].start_seg = i * segments_per_thread;
        thread_data[i].end_seg = (i + 1) * segments_per_thread;
        if (thread_data[i].end_seg > segment_count) {
            thread_data[i].end_seg = segment_count;
        }
        
        thread_data[i].next_multiples = malloc(base_primes_count * sizeof(uint64_t));
        if (!thread_data[i].next_multiples) {
            fprintf(stderr, "Error: Failed to allocate next_multiples array\n");
            exit(EXIT_FAILURE);
        }
        
        /* Initialize next multiples */
        for (uint64_t k = 0; k < base_primes_count; k++) {
            const uint32_t p = base_primes[k];
            thread_data[i].next_multiples[k] = (p >= 3) ? (uint64_t)p * p : 0;
        }
        
        /* Create temporary file for this thread */
        snprintf(thread_data[i].tmp_filename, MAX_PATH, TEMP_FILE_PATTERN, pid, i);
        thread_data[i].outfile = fopen(thread_data[i].tmp_filename, "w");
        if (!thread_data[i].outfile) {
            perror("Failed to open temporary file");
            fprintf(stderr, "Error: Could not create temporary file %s\n", thread_data[i].tmp_filename);
            exit(EXIT_FAILURE);
        }
        setvbuf(thread_data[i].outfile, NULL, _IOFBF, FILE_BUFFER_SIZE);
    }

    /* Define thread function for text generation */
    DWORD WINAPI sieve_segment(LPVOID param) {
        ThreadData *data = (ThreadData*)param;
        data->count = 0;
        
        const uint64_t segment_bytes = cache_size;
        const uint64_t segment_bits = segment_bytes * 8;

        for (uint64_t seg_index = data->start_seg; seg_index < data->end_seg; seg_index++) {
            const uint64_t low = seg_index * (2 * segment_bits);
            uint64_t high = low + 2 * segment_bits - 1;
            if (low > N) break;
            if (high > N) high = N;

            unsigned char *segment = calloc(segment_bytes, 1);
            if (!segment) {
                fprintf(stderr, "Error: Failed to allocate segment memory\n");
                exit(EXIT_FAILURE);
            }

            /* Sieve the segment */
            for (uint64_t k = 0; k < base_primes_count; k++) {
                const uint32_t p = base_primes[k];
                if (p < 3) continue;

                uint64_t next = data->next_multiples[k];
                if (next > high) continue;

                /* Adjust starting point if needed */
                if (next < low) {
                    const uint64_t remainder = low % p;
                    uint64_t start = low - remainder;
                    if (remainder > 0) start += p;
                    if (start % 2 == 0) start += p;
                    next = start;
                }

                /* Mark multiples in current segment */
                const uint64_t start_j = (next - (low + 1)) / 2;
                const uint64_t step = p;
                const uint64_t limit = (high - (low + 1)) / 2;
                
                for (uint64_t j = start_j; j <= limit; j += step) {
                    segment[j >> 3] |= (1 << (j & 7));
                }
                
                data->next_multiples[k] = next + step * ((limit - start_j) / step + 1) * 2;
            }

            /* Write primes to temporary file */
            uint64_t count_segment = 0;
            for (uint64_t j = 0; j < segment_bits; j++) {
                const uint64_t num = low + 1 + 2 * j;
                if (num > N || num < 3) continue;
                
                if (!(segment[j >> 3] & (1 << (j & 7)))) {
                    count_segment++;
                    fprintf(data->outfile, "%llu\n", num);
                }
            }

            data->count += count_segment;
            free(segment);
        }
        return 0;
    }

    /* Create and run threads */
    for (int i = 0; i < num_threads; i++) {
        threads[i] = CreateThread(NULL, 0, sieve_segment, &thread_data[i], 0, NULL);
        if (!threads[i]) {
            fprintf(stderr, "Error: Failed to create thread\n");
            exit(EXIT_FAILURE);
        }
    }

    /* Wait for threads to complete */
    WaitForMultipleObjects(num_threads, threads, TRUE, INFINITE);

    /* Combine results */
    uint64_t total_count = 1;  // Include 2
    FILE *outfile = fopen(filename, "w");
    if (!outfile) {
        perror("Failed to open output file");
        fprintf(stderr, "Error: Could not open output file %s\n", filename);
        exit(EXIT_FAILURE);
    }
    fprintf(outfile, "2\n");  
    
    for (int i = 0; i < num_threads; i++) {
        total_count += thread_data[i].count;
        free(thread_data[i].next_multiples);
        fclose(thread_data[i].outfile);
        CloseHandle(threads[i]);

        /* Merge temporary files */
        FILE *tmpfile = fopen(thread_data[i].tmp_filename, "r");
        if (!tmpfile) {
            perror("Failed to open temporary file for reading");
            fprintf(stderr, "Warning: Could not open temp file %s\n", thread_data[i].tmp_filename);
            continue;
        }
        
        char buffer[FILE_BUFFER_SIZE];
        size_t bytes_read;
        while ((bytes_read = fread(buffer, 1, sizeof(buffer), tmpfile)) > 0) {
            fwrite(buffer, 1, bytes_read, outfile);
        }
        
        fclose(tmpfile);
        if (remove(thread_data[i].tmp_filename) != 0) {
            fprintf(stderr, "Warning: Could not remove temp file %s\n", thread_data[i].tmp_filename);
        }
    }
    fclose(outfile);

    /* Clean up */
    free(threads);
    free(thread_data);
    unlock_memory(base_primes, base_primes_count * sizeof(uint32_t));
    free(base_primes);

    if (!silent) {
        printf("Primes written to %s\n", filename);
        printf("Number of primes up to %llu: %llu\n", N, total_count);
    }
    return total_count;
}

/**
 * Estimate bit array file size
 */
static uint64_t estimate_bitarray_size(uint64_t N) {
    const uint64_t total_bits = (N + 1) / 2;
    const uint64_t total_bytes = (total_bits + 7) / 8;
    return 16 + total_bytes;  // 16-byte header + data
}

/**
 * Generate compact bit array storage for primes
 */
static uint64_t sieve_bitarray(uint64_t N, const char *filename, uint64_t cache_size, bool silent) {
    const uint64_t sqrtN = (uint64_t)ceil(sqrt((double)N));
    const uint64_t segment_bytes = cache_size;
    const uint64_t segment_bits = segment_bytes * 8;
    const uint64_t total_bits = (N + 1) / 2;
    const uint64_t total_bytes = (total_bits + 7) / 8;
    const uint64_t segment_count = (N + 2 * segment_bits - 1) / (2 * segment_bits);

    SYSTEM_INFO sysinfo;
    GetSystemInfo(&sysinfo);
    const int num_threads = sysinfo.dwNumberOfProcessors;
    const int page_size = sysinfo.dwPageSize;

    BasePrimes bp = generate_base_primes(sqrtN);
    uint32_t *base_primes = bp.primes;
    const uint64_t base_primes_count = bp.count;
    optimize_base_primes(bp, &sysinfo);

    /* Precompute starting indices */
    uint64_t *next_multiples = malloc(base_primes_count * sizeof(uint64_t));
    for (uint64_t k = 0; k < base_primes_count; k++) {
        const uint32_t p = base_primes[k];
        next_multiples[k] = (p >= 3) ? (uint64_t)p * p : 0;
    }

    /* Memory availability check */
    uint64_t available_mem = get_available_physical_memory();
    const uint64_t reserved_mem = 500 * 1024 * 1024; /* 500MB system reserve */
    const uint64_t required_mem = total_bytes + 
                                 (segment_bytes * sysinfo.dwNumberOfProcessors) + 
                                 (base_primes_count * sizeof(uint64_t));
    
    unsigned char *global_bitarray = NULL;
    bool use_memory = false;
    
    if (available_mem > reserved_mem && required_mem <= (available_mem - reserved_mem)) {
        global_bitarray = calloc(1, total_bytes);
        if (global_bitarray) {
            /* Pre-fault all pages */
            for (uint64_t i = 0; i < total_bytes; i += page_size) {
                global_bitarray[i] = 0;
            }
            
            /* Lock memory */
            lock_memory(global_bitarray, total_bytes);
            use_memory = true;
        }
    }

    /* File handling variables */
    HANDLE hFile = INVALID_HANDLE_VALUE;
    HANDLE hMap = NULL;
    unsigned char *mapped_buffer = NULL;
    DWORD file_flags = FILE_ATTRIBUTE_TEMPORARY | FILE_FLAG_SEQUENTIAL_SCAN;

    if (!use_memory) {
        /* Create file with optimized flags */
        hFile = CreateFileA(filename, 
                           GENERIC_READ | GENERIC_WRITE,
                           0, 
                           NULL,
                           CREATE_ALWAYS,
                           file_flags,
                           NULL);
        if (hFile == INVALID_HANDLE_VALUE) {
            fprintf(stderr, "Error: CreateFile failed (error %lu)\n", GetLastError());
            exit(EXIT_FAILURE);
        }

        /* Set file size */
        LARGE_INTEGER file_size;
        file_size.QuadPart = 16 + total_bytes;
        if (!SetFilePointerEx(hFile, file_size, NULL, FILE_BEGIN) || 
            !SetEndOfFile(hFile)) {
            fprintf(stderr, "Error: SetEndOfFile failed (error %lu)\n", GetLastError());
            CloseHandle(hFile);
            exit(EXIT_FAILURE);
        }

        /* Create memory mapping */
        hMap = CreateFileMappingA(hFile, 
                                 NULL, 
                                 PAGE_READWRITE, 
                                 file_size.HighPart, 
                                 file_size.LowPart, 
                                 NULL);
        if (!hMap) {
            fprintf(stderr, "Error: CreateFileMapping failed (error %lu)\n", GetLastError());
            CloseHandle(hFile);
            exit(EXIT_FAILURE);
        }

        mapped_buffer = MapViewOfFile(hMap, 
                                    FILE_MAP_WRITE, 
                                    0, 
                                    0, 
                                    file_size.QuadPart);
        if (!mapped_buffer) {
            fprintf(stderr, "Error: MapViewOfFile failed (error %lu)\n", GetLastError());
            CloseHandle(hMap);
            CloseHandle(hFile);
            exit(EXIT_FAILURE);
        }

        /* Write header and initialize */
        uint64_t *header_ptr = (uint64_t*)mapped_buffer;
        header_ptr[0] = N;
        header_ptr[1] = total_bits;
        memset(mapped_buffer + 16, 0, total_bytes);
    }

    typedef struct {
        uint64_t start_seg;
        uint64_t end_seg;
        uint64_t count;
        uint64_t *next_multiples;
        unsigned char *global_bitarray;
        unsigned char *mapped_buffer;
    } ThreadData;

    ThreadData *thread_data = calloc(num_threads, sizeof(ThreadData));
    HANDLE *threads = malloc(num_threads * sizeof(HANDLE));
    if (!thread_data || !threads) {
        fprintf(stderr, "Error: Failed to allocate thread structures\n");
        exit(EXIT_FAILURE);
    }

    for (int i = 0; i < num_threads; i++) {
        thread_data[i].start_seg = i * (segment_count / num_threads);
        thread_data[i].end_seg = (i + 1) * (segment_count / num_threads);
        if (i == num_threads - 1) {
            thread_data[i].end_seg = segment_count;
        }
        
        thread_data[i].next_multiples = malloc(base_primes_count * sizeof(uint64_t));
        memcpy(thread_data[i].next_multiples, next_multiples, base_primes_count * sizeof(uint64_t));
        
        thread_data[i].global_bitarray = global_bitarray;
        thread_data[i].mapped_buffer = mapped_buffer;
    }

    /* Define thread function for bit array generation */
    DWORD WINAPI sieve_segment(LPVOID param) {
        ThreadData *data = (ThreadData*)param;
        data->count = 0;
        
        const uint64_t segment_bytes = cache_size;
        const uint64_t segment_bits = segment_bytes * 8;

        for (uint64_t seg_index = data->start_seg; seg_index < data->end_seg; seg_index++) {
            const uint64_t low = seg_index * (2 * segment_bits);
            uint64_t high = low + 2 * segment_bits - 1;
            if (low > N) break;
            if (high > N) high = N;

            unsigned char *segment = calloc(segment_bytes, 1);
            if (!segment) {
                fprintf(stderr, "Error: Failed to allocate segment memory\n");
                exit(EXIT_FAILURE);
            }

            for (uint64_t k = 0; k < base_primes_count; k++) {
                const uint32_t p = base_primes[k];
                if (p < 3) continue;

                uint64_t next = data->next_multiples[k];
                if (next > high) continue;

                if (next < low) {
                    const uint64_t remainder = low % p;
                    uint64_t start = low - remainder;
                    if (remainder > 0) start += p;
                    if (start % 2 == 0) start += p;
                    next = start;
                }

                const uint64_t start_j = (next - (low + 1)) / 2;
                const uint64_t step = p;
                const uint64_t limit = (high - (low + 1)) / 2;
                
                for (uint64_t j = start_j; j <= limit; j += step) {
                    segment[j >> 3] |= (1 << (j & 7));
                }
                
                data->next_multiples[k] = next + step * ((limit - start_j) / step + 1) * 2;
            }

            uint64_t count_segment = 0;
            for (uint64_t j = 0; j < segment_bits; j++) {
                const uint64_t num = low + 1 + 2 * j;
                if (num > N || num < 3) continue;
                if (!(segment[j >> 3] & (1 << (j & 7)))) {
                    count_segment++;
                }
            }
            data->count += count_segment;

            /* Write segment to buffer */
            const uint64_t offset_bits = seg_index * segment_bits;
            uint64_t bytes_to_write = segment_bytes;
            if (offset_bits + segment_bits > total_bits) {
                bytes_to_write = (total_bits - offset_bits + 7) / 8;
            }
            
            const uint64_t byte_offset = offset_bits / 8;
            
            if (data->global_bitarray) {
                /* In-memory: direct copy */
                memcpy(data->global_bitarray + byte_offset, segment, bytes_to_write);
            } else if (data->mapped_buffer) {
                /* Disk: memory-mapped copy */
                memcpy(data->mapped_buffer + 16 + byte_offset, segment, bytes_to_write);
            }

            free(segment);
        }
        return 0;
    }

    for (int i = 0; i < num_threads; i++) {
        threads[i] = CreateThread(NULL, 0, sieve_segment, &thread_data[i], 0, NULL);
        if (!threads[i]) {
            fprintf(stderr, "Error: Failed to create thread\n");
            exit(EXIT_FAILURE);
        }
    }

    WaitForMultipleObjects(num_threads, threads, TRUE, INFINITE);

    /* Cleanup and finalization */
    uint64_t total_count = 1;
    for (int i = 0; i < num_threads; i++) {
        total_count += thread_data[i].count;
        free(thread_data[i].next_multiples);
        CloseHandle(threads[i]);
    }

    free(threads);
    free(thread_data);

    /* Handle in-memory case */
    if (use_memory) {
        FILE *outfile = fopen(filename, "wb");
        if (!outfile) {
            perror("Failed to open output file");
            fprintf(stderr, "Error: Could not open %s\n", filename);
        } else {
            const uint64_t header[2] = {N, total_bits};
            if (fwrite(header, sizeof(header), 1, outfile) != 1) {
                perror("Header write failed");
            }
            if (fwrite(global_bitarray, 1, total_bytes, outfile) != total_bytes) {
                perror("Data write failed");
            }
            fclose(outfile);
        }

        /* Unlock and free global bitarray */
        unlock_memory(global_bitarray, total_bytes);
        free(global_bitarray);
    } 
    /* Handle disk-based case */
    else {
        if (mapped_buffer) {
            FlushViewOfFile(mapped_buffer, 0);
            UnmapViewOfFile(mapped_buffer);
        }
        if (hMap) {
            CloseHandle(hMap);
        }
        if (hFile != INVALID_HANDLE_VALUE) {
            CloseHandle(hFile);
        }
    }

    /* Unlock and free base primes */
    unlock_memory(base_primes, base_primes_count * sizeof(uint32_t));
    free(base_primes);
    free(next_multiples);

    if (!silent) {
        printf("Compact prime storage written to %s\n", filename);
        printf("Total storage: %llu bytes (%.2f MB)\n", 
               16 + total_bytes, 
               (16.0 + total_bytes) / (1024 * 1024));
        printf("Number of primes up to %llu: %llu\n", N, total_count);
    }
    return total_count;
}

/**
 * Query prime status from bit array file
 */
static void query_bitarray(const char *filename, uint64_t n) {
    FILE *file = fopen(filename, "rb");
    if (!file) {
        perror("File open failed");
        return;
    }
    
    /* Read header */
    uint64_t header[2];
    if (fread(header, sizeof(header), 1, file) != 1) {
        perror("Header read failed");
        fclose(file);
        return;
    }
    
    const uint64_t N = header[0];
    const uint64_t total_bits = header[1];
    
    /* Validate input */
    if (n > N) {
        printf("Error: %llu exceeds limit %llu\n", n, N);
        fclose(file);
        return;
    }
    
    /* Handle special cases */
    if (n == 2) {
        printf("%llu is prime\n", n);
        fclose(file);
        return;
    }
    if (n % 2 == 0 || n < 2) {
        printf("%llu is not prime\n", n);
        fclose(file);
        return;
    }
    
    /* Calculate bit position */
    const uint64_t index = (n - 1) / 2;
    const uint64_t byte_offset = sizeof(header) + index / 8;
    const uint8_t bit_offset = index % 8;
    
    /* Read relevant byte - use 64-bit positioning */
    if (_fseeki64(file, byte_offset, SEEK_SET) != 0) {
        perror("File seek failed");
        fclose(file);
        return;
    }
    
    uint8_t byte;
    if (fread(&byte, 1, 1, file) != 1) {
        perror("Data read failed");
        fclose(file);
        return;
    }
    
    /* Check prime status */
    if (((byte >> bit_offset) & 1) == 0) {
        printf("%llu is prime\n", n);
    } else {
        printf("%llu is not prime\n", n);
    }
    
    fclose(file);
}

/**
 * Format file size for human-readable output
 */
static void format_file_size(uint64_t bytes, char* buffer, size_t buffer_size) {
    const char* units[] = {"B", "KB", "MB", "GB", "TB"};
    size_t unit_index = 0;
    double size = (double)bytes;

    while (size >= 1024 && unit_index < sizeof(units)/sizeof(units[0]) - 1) {
        size /= 1024;
        unit_index++;
    }

    snprintf(buffer, buffer_size, "%.2f %s", size, units[unit_index]);
}

/**
 * Run benchmark for all three operations
 */
static BenchmarkResults run_benchmark(uint64_t N, uint64_t cache_size) {
    BenchmarkResults results = {0};
    double times_count[BENCHMARK_RUNS] = {0};
    double times_text[BENCHMARK_RUNS] = {0};
    double times_bitarray[BENCHMARK_RUNS] = {0};
    double thread_times_sum[MAX_THREADS] = {0};
    
    SYSTEM_INFO sysinfo;
    GetSystemInfo(&sysinfo);
    results.num_threads = sysinfo.dwNumberOfProcessors;
    
    /* Create temporary filenames */
    char temp_text_file[MAX_FILENAME_LENGTH];
    char temp_bitarray_file[MAX_FILENAME_LENGTH];
    snprintf(temp_text_file, sizeof(temp_text_file), "benchmark_text_%d.tmp", GetCurrentProcessId());
    snprintf(temp_bitarray_file, sizeof(temp_bitarray_file), "benchmark_bitarray_%d.tmp", GetCurrentProcessId());
    
    printf("\nRunning benchmark for N = %llu (%d threads)...\n", N, results.num_threads);
    
    /* Run count benchmark */
    printf("Benchmarking prime counting...\n");
    for (int i = 0; i < BENCHMARK_RUNS; i++) {
        double thread_times_this_run[MAX_THREADS] = {0};
        clock_t start = clock();
        results.prime_count = sieve_count(N, cache_size, true, thread_times_this_run);
        clock_t end = clock();
        times_count[i] = (double)(end - start) / CLOCKS_PER_SEC;
        printf("  Run %d: %.3f seconds\n", i+1, times_count[i]);
        
        /* Sum thread times for averaging */
        for (int t = 0; t < results.num_threads; t++) {
            thread_times_sum[t] += thread_times_this_run[t];
        }
    }
    
    /* Calculate average thread times */
    for (int t = 0; t < results.num_threads; t++) {
        results.count_thread_times[t] = thread_times_sum[t] / BENCHMARK_RUNS;
    }
    
    /* Run text generation benchmark */
    printf("Benchmarking text generation...\n");
    for (int i = 0; i < BENCHMARK_RUNS; i++) {
        clock_t start = clock();
        sieve_text(N, temp_text_file, cache_size, true);
        clock_t end = clock();
        times_text[i] = (double)(end - start) / CLOCKS_PER_SEC;
        printf("  Run %d: %.3f seconds\n", i+1, times_text[i]);
        remove(temp_text_file);
    }
    
    /* Run bitarray generation benchmark */
    printf("Benchmarking bitarray generation...\n");
    for (int i = 0; i < BENCHMARK_RUNS; i++) {
        clock_t start = clock();
        sieve_bitarray(N, temp_bitarray_file, cache_size, true);
        clock_t end = clock();
        times_bitarray[i] = (double)(end - start) / CLOCKS_PER_SEC;
        printf("  Run %d: %.3f seconds\n", i+1, times_bitarray[i]);
        remove(temp_bitarray_file);
    }
    
    /* Calculate mean times */
    for (int i = 0; i < BENCHMARK_RUNS; i++) {
        results.count_time += times_count[i];
        results.text_time += times_text[i];
        results.bitarray_time += times_bitarray[i];
    }
    
    results.count_time /= BENCHMARK_RUNS;
    results.text_time /= BENCHMARK_RUNS;
    results.bitarray_time /= BENCHMARK_RUNS;
    
    return results;
}

/**
 * Display benchmark results in a table
 */
static void display_benchmark_results(BenchmarkResults results, uint64_t N) {
    const char* separator = "--------------------------------------------------------------";
    const char* header_separator = "--------------------";
    
    printf("\nBenchmark Results (N = %llu, %d threads)\n", N, results.num_threads);
    printf("%s\n", separator);
    printf("%-20s | %-10s | %-20s\n", "Operation", "Time (s)", "Time per prime (ns)");
    printf("%s\n", separator);
    
    /* Calculate metrics for counting */
    double count_time_per_prime = (results.count_time * 1e9) / results.prime_count;
    printf("%-20s | %10.3f | %20.2f\n", 
           "Count", results.count_time, count_time_per_prime);
    
    /* Calculate metrics for text generation */
    double text_time_per_prime = (results.text_time * 1e9) / results.prime_count;
    printf("%-20s | %10.3f | %20.2f\n", 
           "Text Generation", results.text_time, text_time_per_prime);
    
    /* Calculate metrics for bitarray generation */
    double bitarray_time_per_prime = (results.bitarray_time * 1e9) / results.prime_count;
    printf("%-20s | %10.3f | %20.2f\n", 
           "Bitarray Generation", results.bitarray_time, bitarray_time_per_prime);
    
    printf("%s\n", separator);
    printf("Total primes: %llu\n", results.prime_count);
    
    /* Display per-thread times for counting */
    printf("\nPer-Thread CPU Times for Counting Operation\n");
    printf("%s\n", header_separator);
    printf("%-9s | %10s\n", "Thread ID", "Time (s)");
    printf("%s\n", header_separator);
    for (int t = 0; t < results.num_threads; t++) {
        printf("%9d | %10.3f\n", t, results.count_thread_times[t]);
    }
    printf("%s\n", header_separator);
    printf("Note: Thread times are CPU time (user + kernel) averaged over %d runs\n", BENCHMARK_RUNS);
}

int main() {
    SYSTEM_INFO sysinfo;
    GetSystemInfo(&sysinfo);
    printf("Detected logical processors: %d\n",sysinfo.dwNumberOfProcessors);

    const uint64_t cache_size = get_l1_cache_size();
    printf("Detected L1 cache size: %llu bytes (%.2f KB)", cache_size, (double)cache_size / 1024);
    
    while(1) 
    {
        printf("\n\nWhat would you like to do?\n");
        printf("----------------------------------------\n");
        printf("1. Count primes up to N\n");
        printf("2. Generate primes list (text file)\n");
        printf("3. Generate compact bit array (fastest)\n");
        printf("4. Query existing bit array\n");
        printf("5. Benchmark generators\n");
        printf("0. Exit\n");
        
        /* Get user option */
        uint64_t option;
        printf("Select option: ");
        while (!get_input(&option)) {
            printf("Select valid option (1-5): ");
        }

        uint64_t input;
        double prime_estimate;

        if (option != 0)
        {
            /* Get input number */
            printf("Enter number: ");
            while (!get_input(&input)) {
                printf("Enter valid number: ");
            }
        

            /* Estimate prime count for user */
            prime_estimate = 0;
            if (option > 0 && option < 4) {
                prime_estimate = input / (log((double)input) - 1);
                
                char estimated_primes[20];
                sprintf(estimated_primes, "%.*g", RESOLUTION, prime_estimate);
                printf("Attempting to find approximately %s primes...\n", estimated_primes);
            }
        }
        clock_t start_time;
        
        switch (option) {
            case 0:
                exit(0);
                break;
            case 1:  /* Count primes */
                start_time = clock();
                sieve_count(input, cache_size, false, NULL);
                break;
                
            case 2: {  /* Generate text file */
                uint64_t text_size = estimate_text_file_size(input, (uint64_t)prime_estimate);
                char text_size_str[32];
                format_file_size(text_size, text_size_str, sizeof(text_size_str));
                printf("Estimated text file size:   %s\n", text_size_str);

                char filename[MAX_FILENAME_LENGTH];
                printf("Output filename: ");
                if (fgets(filename, sizeof(filename), stdin)) {
                    filename[strcspn(filename, "\n")] = 0;  /* Remove newline */
                    start_time = clock();
                    sieve_text(input, filename, cache_size, false);
                }
                break;
            }
                
            case 3: {  /* Generate bit array */
                uint64_t bitarray_size = estimate_bitarray_size(input);
                char bitarray_size_str[32];
                format_file_size(bitarray_size, bitarray_size_str, sizeof(bitarray_size_str));
                printf("Estimated bit array size:   %s\n", bitarray_size_str);

                char filename[MAX_FILENAME_LENGTH];
                printf("Output filename: ");
                if (fgets(filename, sizeof(filename), stdin)) {
                    filename[strcspn(filename, "\n")] = 0;
                    start_time = clock();
                    sieve_bitarray(input, filename, cache_size, false);
                }
                break;
            }
                
            case 4: {  /* Query bit array */
                char filename[MAX_FILENAME_LENGTH];
                printf("Bit array file: ");
                if (fgets(filename, sizeof(filename), stdin)) {
                    filename[strcspn(filename, "\n")] = 0;
                    start_time = clock();
                    query_bitarray(filename, input);
                }
                break;
            }
                
            case 5: {  /* Benchmark */
                start_time = clock();
                BenchmarkResults results = run_benchmark(input, cache_size);
                display_benchmark_results(results, input);
                break;
            }
                
            default:
                printf("Invalid option selected.\n");
        }
        
        /* Display execution time */
        if (option != 5) {  /* Don't show for benchmark (already shown in table) */
            const double elapsed = ((double)(clock() - start_time)) / CLOCKS_PER_SEC;
            if (elapsed < 0.001) {
                printf("Finished in under 1ms!\n");
            } else {
                printf("Finished in %.3fs.\n", elapsed);
            }
        }
    }
    return EXIT_SUCCESS;
}