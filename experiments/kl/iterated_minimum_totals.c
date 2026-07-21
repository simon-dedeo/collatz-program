/* Stream exact iterated fiber-minimum totals from a one-dimensional NPY file.

   This is the bounded memory-mapped native core used by
   verify_iterated_minimum_growth.py.  Integer inputs are positive little-
   endian int64 arrays.  Every total is accumulated in unsigned 128-bit
   arithmetic; the caller performs the larger cross-products with Python
   integers.  Float64 mode is deliberately separate and supplies orientation
   only for the uncertified k=20 candidate.
*/

#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

typedef __uint128_t u128;

static void die(const char *message) {
    fprintf(stderr, "iterated_minimum_totals: %s\n", message);
    exit(EXIT_FAILURE);
}

static void print_u128(u128 value) {
    char digits[64];
    size_t count = 0;
    do {
        digits[count++] = (char)('0' + value % 10);
        value /= 10;
    } while (value != 0);
    while (count > 0) {
        putchar(digits[--count]);
    }
}

static uint64_t min3_u64(uint64_t a, uint64_t b, uint64_t c) {
    uint64_t result = a < b ? a : b;
    return result < c ? result : c;
}

static double min3_double(double a, double b, double c) {
    double result = a < b ? a : b;
    return result < c ? result : c;
}

static void check_power_of_three(uint64_t length) {
    if (length == 0) {
        die("empty input");
    }
    while (length % 3 == 0) {
        length /= 3;
    }
    if (length != 1) {
        die("array length is not a power of three");
    }
}

static void reduce_integer(const int64_t *input, uint64_t length) {
    u128 total = 0;
    uint64_t third = length / 3;
    uint64_t *profile = NULL;
    if (length >= 3) {
        profile = malloc((size_t)third * sizeof(*profile));
        if (profile == NULL) {
            die("could not allocate first minimum profile");
        }
    }

    for (uint64_t index = 0; index < length; ++index) {
        if (input[index] <= 0) {
            die("integer input is not strictly positive");
        }
        total += (uint64_t)input[index];
    }
    printf("0 %" PRIu64 " ", length);
    print_u128(total);
    putchar('\n');

    unsigned depth = 1;
    while (length >= 3) {
        third = length / 3;
        u128 next_total = 0;
        if (depth == 1) {
            for (uint64_t index = 0; index < third; ++index) {
                uint64_t value = min3_u64(
                    (uint64_t)input[index],
                    (uint64_t)input[index + third],
                    (uint64_t)input[index + 2 * third]
                );
                profile[index] = value;
                next_total += value;
            }
        } else {
            for (uint64_t index = 0; index < third; ++index) {
                uint64_t value = min3_u64(
                    profile[index],
                    profile[index + third],
                    profile[index + 2 * third]
                );
                profile[index] = value;
                next_total += value;
            }
        }
        length = third;
        printf("%u %" PRIu64 " ", depth, length);
        print_u128(next_total);
        putchar('\n');
        ++depth;
    }
    free(profile);
}

static void reduce_float(const double *input, uint64_t length) {
    long double total = 0.0L;
    uint64_t third = length / 3;
    double *profile = NULL;
    if (length >= 3) {
        profile = malloc((size_t)third * sizeof(*profile));
        if (profile == NULL) {
            die("could not allocate first floating minimum profile");
        }
    }
    for (uint64_t index = 0; index < length; ++index) {
        if (!(input[index] > 0.0) || !isfinite(input[index])) {
            die("floating input is not strictly positive and finite");
        }
        total += (long double)input[index];
    }
    printf("0 %" PRIu64 " %.21Lg\n", length, total);

    unsigned depth = 1;
    while (length >= 3) {
        third = length / 3;
        long double next_total = 0.0L;
        if (depth == 1) {
            for (uint64_t index = 0; index < third; ++index) {
                double value = min3_double(
                    input[index], input[index + third], input[index + 2 * third]
                );
                profile[index] = value;
                next_total += (long double)value;
            }
        } else {
            for (uint64_t index = 0; index < third; ++index) {
                double value = min3_double(
                    profile[index],
                    profile[index + third],
                    profile[index + 2 * third]
                );
                profile[index] = value;
                next_total += (long double)value;
            }
        }
        length = third;
        printf("%u %" PRIu64 " %.21Lg\n", depth, length, next_total);
        ++depth;
    }
    free(profile);
}

int main(int argc, char **argv) {
    if (argc != 3 || (strcmp(argv[1], "integer") != 0 && strcmp(argv[1], "float") != 0)) {
        die("usage: iterated_minimum_totals {integer|float} FILE.npy");
    }
#if __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
    die("this bounded helper currently requires a little-endian host");
#endif

    int descriptor = open(argv[2], O_RDONLY);
    if (descriptor < 0) {
        die(strerror(errno));
    }
    struct stat status;
    if (fstat(descriptor, &status) != 0 || status.st_size < 16) {
        die("could not stat a nonempty NPY file");
    }
    size_t file_size = (size_t)status.st_size;
    unsigned char *mapping = mmap(NULL, file_size, PROT_READ, MAP_PRIVATE, descriptor, 0);
    if (mapping == MAP_FAILED) {
        die("mmap failed");
    }
    if (memcmp(mapping, "\x93NUMPY", 6) != 0) {
        die("input does not have the NPY magic header");
    }

    unsigned major = mapping[6];
    size_t prefix = 0;
    size_t header_length = 0;
    if (major == 1) {
        prefix = 10;
        header_length = (size_t)mapping[8] | ((size_t)mapping[9] << 8);
    } else if (major == 2 || major == 3) {
        prefix = 12;
        header_length = (size_t)mapping[8]
            | ((size_t)mapping[9] << 8)
            | ((size_t)mapping[10] << 16)
            | ((size_t)mapping[11] << 24);
    } else {
        die("unsupported NPY version");
    }
    if (prefix + header_length > file_size || header_length >= 4096) {
        die("invalid or unexpectedly large NPY header");
    }
    char header[4096];
    memcpy(header, mapping + prefix, header_length);
    header[header_length] = '\0';
    if (strstr(header, "'fortran_order': False") == NULL) {
        die("expected a C-order NPY array");
    }
    const char *shape = strstr(header, "'shape': (");
    if (shape == NULL) {
        die("could not parse the NPY shape");
    }
    shape += strlen("'shape': (");
    errno = 0;
    char *end = NULL;
    uint64_t length = strtoull(shape, &end, 10);
    if (errno != 0 || end == shape || strstr(end, ",)") == NULL) {
        die("expected a one-dimensional NPY shape");
    }
    check_power_of_three(length);

    size_t data_offset = prefix + header_length;
    if (length > (file_size - data_offset) / 8 || data_offset + (size_t)length * 8 != file_size) {
        die("NPY data size does not match its shape");
    }
    if (strcmp(argv[1], "integer") == 0) {
        if (strstr(header, "'descr': '<i8'") == NULL) {
            die("integer mode requires little-endian int64 data");
        }
        reduce_integer((const int64_t *)(mapping + data_offset), length);
    } else {
        if (strstr(header, "'descr': '<f8'") == NULL) {
            die("float mode requires little-endian float64 data");
        }
        reduce_float((const double *)(mapping + data_offset), length);
    }

    if (munmap(mapping, file_size) != 0 || close(descriptor) != 0) {
        die("failed to close the mapped input");
    }
    return EXIT_SUCCESS;
}
