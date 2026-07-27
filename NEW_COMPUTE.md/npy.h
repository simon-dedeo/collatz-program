#ifndef NEW_COMPUTE_NPY_H
#define NEW_COMPUTE_NPY_H

#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

typedef enum { NPY_F64, NPY_I64, NPY_U64 } npy_kind;

typedef struct {
    int fd;
    void *mapping;
    size_t mapping_size;
    const void *data;
    uint64_t count;
    npy_kind kind;
} npy_view;

static uint32_t npy_le32(const unsigned char *p, unsigned n) {
    uint32_t v = 0;
    for (unsigned i = 0; i < n; ++i) v |= (uint32_t)p[i] << (8U * i);
    return v;
}

static int npy_open_1d(const char *path, npy_view *view) {
    memset(view, 0, sizeof(*view));
    view->fd = open(path, O_RDONLY);
    if (view->fd < 0) return -1;
    struct stat st;
    if (fstat(view->fd, &st) || st.st_size < 16) return -2;
    view->mapping_size = (size_t)st.st_size;
    view->mapping = mmap(NULL, view->mapping_size, PROT_READ, MAP_PRIVATE, view->fd, 0);
    if (view->mapping == MAP_FAILED) return -3;
    const unsigned char *p = (const unsigned char *)view->mapping;
    if (memcmp(p, "\x93NUMPY", 6)) return -4;
    unsigned version = p[6];
    unsigned hbytes = version == 1 ? 2 : ((version == 2 || version == 3) ? 4 : 0);
    if (!hbytes) return -5;
    size_t prefix = 8 + hbytes;
    uint32_t hlen = npy_le32(p + 8, hbytes);
    if (prefix + hlen > view->mapping_size || hlen >= 4096) return -6;
    char header[4096];
    memcpy(header, p + prefix, hlen);
    header[hlen] = 0;
    if (!strstr(header, "'fortran_order': False")) return -7;
    if (strstr(header, "'<f8'") || strstr(header, "'|f8'") || strstr(header, "'=f8'"))
        view->kind = NPY_F64;
    else if (strstr(header, "'<i8'") || strstr(header, "'=i8'"))
        view->kind = NPY_I64;
    else if (strstr(header, "'<u8'") || strstr(header, "'=u8'"))
        view->kind = NPY_U64;
    else return -8;
    const char *shape = strstr(header, "'shape': (");
    if (!shape) return -9;
    shape += strlen("'shape': (");
    errno = 0;
    char *end = NULL;
    unsigned long long count = strtoull(shape, &end, 10);
    if (errno || end == shape || !strstr(end, ",)")) return -10;
    size_t offset = prefix + hlen;
    if (count > (SIZE_MAX - offset) / 8 || offset + (size_t)count * 8 != view->mapping_size)
        return -11;
    view->count = (uint64_t)count;
    view->data = p + offset;
    return 0;
}

static double npy_get(const npy_view *v, uint64_t i) {
    if (v->kind == NPY_F64) return ((const double *)v->data)[i];
    if (v->kind == NPY_I64) return (double)((const int64_t *)v->data)[i];
    return (double)((const uint64_t *)v->data)[i];
}

static void npy_close(npy_view *v) {
    if (v->mapping && v->mapping != MAP_FAILED) munmap(v->mapping, v->mapping_size);
    if (v->fd >= 0) close(v->fd);
    memset(v, 0, sizeof(*v));
    v->fd = -1;
}

#endif
