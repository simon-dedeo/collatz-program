#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <float.h>
#include <math.h>
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

static void fail(const char *s) { fprintf(stderr, "kl_soft_spectrum: %s\n", s); exit(2); }

static int load_checkpoint(const char *path, double *x, uint64_t n) {
    if (!strcmp(path, "-")) return 0;
    FILE *f = fopen(path, "rb");
    if (!f) return 0;
    int ok = fread(x, sizeof(double), (size_t)n, f) == n && fgetc(f) == EOF;
    fclose(f);
    if (!ok) fail("checkpoint has the wrong byte length");
    return 1;
}

static void save_checkpoint(const char *path, const double *x, uint64_t n) {
    if (!strcmp(path, "-")) return;
    size_t len = strlen(path);
    char *tmp = malloc(len + 5);
    if (!tmp) fail("checkpoint path allocation failed");
    memcpy(tmp, path, len); memcpy(tmp + len, ".tmp", 5);
    FILE *f = fopen(tmp, "wb");
    if (!f || fwrite(x, sizeof(double), (size_t)n, f) != n || fclose(f) || rename(tmp, path))
        fail("could not atomically save checkpoint");
    free(tmp);
}

static uint64_t pow3u(unsigned e) {
    uint64_t x = 1;
    for (unsigned i = 0; i < e; ++i) {
        if (x > UINT64_MAX / 3) fail("level is too large");
        x *= 3;
    }
    return x;
}

static inline double mean_minus_beta(double a, double b, double c, double beta) {
    double m = fmin(a, fmin(b, c));
    double sum = pow(m / a, beta) + pow(m / b, beta) + pow(m / c, beta);
    return m * exp(-log(sum / 3.0) / beta);
}

int main(int argc, char **argv) {
    if (argc != 8) fail("usage: LEVEL LAMBDA BETA MAX_ITER LOG_TOL OUTPUT_TSV OUTPUT_VECTOR_OR_DASH");
    unsigned level = (unsigned)strtoul(argv[1], NULL, 10);
    double lambda = strtod(argv[2], NULL), beta = strtod(argv[3], NULL);
    unsigned max_iter = (unsigned)strtoul(argv[4], NULL, 10);
    double tol = strtod(argv[5], NULL);
    if (level < 2 || !(lambda > 1 && lambda < 2) || !(beta > 0) || max_iter < 1 || !(tol > 0))
        fail("invalid arguments");
    uint64_t n = pow3u(level - 1), third = n / 3;
    if (n > SIZE_MAX / sizeof(double)) fail("vector size exceeds address space");
    double *x = NULL, *y = NULL;
    if (posix_memalign((void **)&x, 64, (size_t)n * sizeof(double)) ||
        posix_memalign((void **)&y, 64, (size_t)n * sizeof(double))) fail("allocation failed");
    int resumed = load_checkpoint(argv[7], x, n);
    if (!resumed) {
#pragma omp parallel for schedule(static)
        for (uint64_t i = 0; i < n; ++i) x[i] = 1.0;
    }
    const double alpha = log(3.0) / log(2.0);
    const double tau = pow(lambda, -2.0), w2 = pow(lambda, alpha - 2.0), w8 = pow(lambda, alpha - 1.0);
    const double annealed = tau + (w2 + w8) / 3.0;
    FILE *out = fopen(argv[6], "a");
    if (!out) fail(strerror(errno));
    setvbuf(out, NULL, _IOLBF, 0);
    fprintf(out, "# level=%u states=%llu lambda=%.17g beta=%.17g threads=%d annealed=%.17g resumed=%d\n",
            level, (unsigned long long)n, lambda, beta, omp_get_max_threads(), annealed, resumed);
    double lower = 0, upper = DBL_MAX;
    unsigned iter;
    double started = omp_get_wtime();
    for (iter = 1; iter <= max_iter; ++iter) {
        lower = DBL_MAX; upper = 0;
        int bad = 0;
#pragma omp parallel for schedule(static) reduction(min:lower) reduction(max:upper) reduction(|:bad)
        for (uint64_t i = 0; i < n; ++i) {
            double v = tau * x[(4 * i + 2) % n];
            unsigned kind = (unsigned)(i % 3);
            if (kind != 1) {
                uint64_t base = kind == 0 ? (4 * (i / 3)) % third
                                          : (2 * ((i - 2) / 3) + 1) % third;
                double m = mean_minus_beta(x[base], x[base + third], x[base + 2 * third], beta);
                v += (kind == 0 ? w2 : w8) * m;
            }
            y[i] = v;
            double r = v / x[i];
            if (!(v > 0) || !isfinite(v) || !(r > 0) || !isfinite(r)) bad = 1;
            if (r < lower) lower = r;
            if (r > upper) upper = r;
        }
        if (bad || !(lower <= upper)) fail("nonpositive or nonfinite iteration");
        double width = log(upper / lower);
        if (iter == 1 || iter % 25 == 0 || width <= tol)
            fprintf(out, "%u\t%.17g\t%.17g\t%.17g\t%.9f\n", iter, lower, upper, width, omp_get_wtime() - started);
#pragma omp parallel for schedule(static)
        for (uint64_t i = 0; i < n; ++i) y[i] /= upper;
        double *tmp = x; x = y; y = tmp;
        if (iter % 250 == 0) save_checkpoint(argv[7], x, n);
        if (width <= tol) break;
    }
    double midpoint = sqrt(lower * upper), threshold = exp(log(3.0) / beta);
    fprintf(out, "RESULT\t%u\t%llu\t%.17g\t%.17g\t%.17g\t%u\t%.17g\t%.17g\t%.17g\t%s\n",
            level, (unsigned long long)n, lambda, beta, midpoint, iter, lower, upper,
            threshold, lower > threshold ? "CROSSES_FLOATING" : "NO_CROSSING");
    fclose(out);
    save_checkpoint(argv[7], x, n);
    free(x); free(y);
    return 0;
}
