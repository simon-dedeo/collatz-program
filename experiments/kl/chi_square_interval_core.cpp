#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

#ifndef __SIZEOF_INT128__
#error "chi_square_interval_core requires a compiler with unsigned __int128"
#endif

// Bulk exact arithmetic for verify_chi_square_envelope.py.  The Python driver
// checks the manifest, shape, dtype, positivity, and SHA-256 before invoking
// this helper.  This program handles the large levels while every parent mass
// is small enough that N <= 6 P^2 fits in unsigned 128-bit arithmetic.  It then
// writes the remaining (short) hierarchy to a raw uint64 file for Python
// bigint completion.

using u128 = unsigned __int128;

namespace {

constexpr std::uint64_t kSquareSumSafeParent = 7530851732716320752ULL;

struct Row {
    int depth;
    u128 lower;
    u128 upper;
    std::uint64_t parent_count;
    std::uint64_t nonzero_remainders;
};

struct NpyMetadata {
    std::string path;
    std::uint64_t count;
    std::uint64_t data_offset;
};

struct FirstPass {
    std::vector<std::uint64_t> parents;
    Row row;
    u128 total;
};

constexpr u128 kU128Max = ~static_cast<u128>(0);

void checked_add(u128 &target, u128 value, const char *label) {
    if (kU128Max - target < value) {
        throw std::overflow_error(std::string(label) + " exceeds unsigned 128-bit range");
    }
    target += value;
}

std::string decimal(u128 value) {
    if (value == 0) {
        return "0";
    }
    std::string digits;
    while (value != 0) {
        digits.push_back(static_cast<char>('0' + value % 10));
        value /= 10;
    }
    std::reverse(digits.begin(), digits.end());
    return digits;
}

std::uint32_t little_endian_u32(const unsigned char *bytes, int count) {
    std::uint32_t value = 0;
    for (int i = 0; i < count; ++i) {
        value |= static_cast<std::uint32_t>(bytes[i]) << (8 * i);
    }
    return value;
}

NpyMetadata read_npy_metadata(const std::string &path, int k) {
    std::uint64_t expected = 1;
    for (int i = 0; i < k - 1; ++i) {
        if (expected > std::numeric_limits<std::uint64_t>::max() / 3) {
            throw std::runtime_error("level size overflows uint64");
        }
        expected *= 3;
    }

    std::ifstream input(path, std::ios::binary);
    if (!input) {
        throw std::runtime_error("cannot open input NPY");
    }
    unsigned char prefix[8] = {};
    input.read(reinterpret_cast<char *>(prefix), sizeof(prefix));
    const unsigned char expected_magic[6] = {0x93, 'N', 'U', 'M', 'P', 'Y'};
    if (!input || !std::equal(prefix, prefix + 6, expected_magic)) {
        throw std::runtime_error("invalid NPY magic");
    }
    const unsigned version = prefix[6];
    unsigned char length_bytes[4] = {};
    const int length_size = version == 1 ? 2 : (version == 2 || version == 3 ? 4 : 0);
    if (length_size == 0) {
        throw std::runtime_error("unsupported NPY version");
    }
    input.read(reinterpret_cast<char *>(length_bytes), length_size);
    const std::uint32_t header_length = little_endian_u32(length_bytes, length_size);
    std::string header(header_length, ' ');
    input.read(header.data(), static_cast<std::streamsize>(header_length));
    if (!input || header.find("'<i8'") == std::string::npos ||
        header.find("'fortran_order': False") == std::string::npos) {
        throw std::runtime_error("expected a C-order little-endian int64 NPY");
    }

    const std::streampos data_position = input.tellg();
    if (data_position < 0) {
        throw std::runtime_error("failed to locate NPY payload");
    }
    input.seekg(0, std::ios::end);
    const std::streampos end_position = input.tellg();
    const auto expected_end = static_cast<std::uint64_t>(data_position) +
        expected * sizeof(std::uint64_t);
    if (end_position < 0 || static_cast<std::uint64_t>(end_position) != expected_end) {
        throw std::runtime_error("NPY payload length does not match the requested level");
    }
    return {path, expected, static_cast<std::uint64_t>(data_position)};
}

bool accumulate_parent(
    std::uint64_t x0,
    std::uint64_t x1,
    std::uint64_t x2,
    std::uint64_t &parent_output,
    u128 &lower,
    u128 &upper,
    std::uint64_t &nonzero_remainders) {
    const u128 parent = static_cast<u128>(x0) + x1 + x2;
    if (parent == 0) {
        throw std::runtime_error("parent mass is zero");
    }
    if (parent > kSquareSumSafeParent) {
        return false;
    }
    parent_output = static_cast<std::uint64_t>(parent);
    const u128 three_x0 = 3 * static_cast<u128>(x0);
    const u128 three_x1 = 3 * static_cast<u128>(x1);
    const u128 three_x2 = 3 * static_cast<u128>(x2);
    const u128 d0 = three_x0 >= parent ? three_x0 - parent : parent - three_x0;
    const u128 d1 = three_x1 >= parent ? three_x1 - parent : parent - three_x1;
    const u128 d2 = three_x2 >= parent ? three_x2 - parent : parent - three_x2;
    u128 numerator = d0 * d0;
    checked_add(numerator, d1 * d1, "parent square sum");
    checked_add(numerator, d2 * d2, "parent square sum");
    const u128 quotient = numerator / parent;
    const bool has_remainder = numerator % parent != 0;
    checked_add(lower, quotient, "lower interval accumulator");
    checked_add(upper, quotient + has_remainder, "upper interval accumulator");
    nonzero_remainders += has_remainder;
    return true;
}

FirstPass stream_first_depth(const NpyMetadata &npy, int depth) {
    if (npy.count % 3 != 0) {
        throw std::runtime_error("NPY genealogy length is not divisible by three");
    }
    const std::uint64_t parent_count = npy.count / 3;
    std::vector<std::uint64_t> parents(parent_count);
    std::ifstream streams[3];
    for (int digit = 0; digit < 3; ++digit) {
        streams[digit].open(npy.path, std::ios::binary);
        if (!streams[digit]) {
            throw std::runtime_error("cannot reopen input NPY");
        }
        const std::uint64_t digit_offset =
            npy.data_offset + digit * parent_count * sizeof(std::uint64_t);
        streams[digit].seekg(static_cast<std::streamoff>(digit_offset));
        if (!streams[digit]) {
            throw std::runtime_error("failed to seek to NPY digit block");
        }
    }

    constexpr std::uint64_t kBlockSize = 1U << 20;
    std::vector<std::uint64_t> blocks[3];
    for (auto &block : blocks) {
        block.resize(kBlockSize);
    }
    u128 total = 0;
    u128 lower = 0;
    u128 upper = 0;
    std::uint64_t nonzero_remainders = 0;
    for (std::uint64_t start = 0; start < parent_count; start += kBlockSize) {
        const std::uint64_t count = std::min(kBlockSize, parent_count - start);
        const auto byte_count = static_cast<std::streamsize>(
            count * sizeof(std::uint64_t));
        for (int digit = 0; digit < 3; ++digit) {
            streams[digit].read(
                reinterpret_cast<char *>(blocks[digit].data()), byte_count);
            if (!streams[digit]) {
                throw std::runtime_error("short NPY digit block");
            }
        }
        for (std::uint64_t offset = 0; offset < count; ++offset) {
            const std::uint64_t x0 = blocks[0][offset];
            const std::uint64_t x1 = blocks[1][offset];
            const std::uint64_t x2 = blocks[2][offset];
            checked_add(total, static_cast<u128>(x0) + x1 + x2, "total mass");
            if (!accumulate_parent(
                    x0,
                    x1,
                    x2,
                    parents[start + offset],
                    lower,
                    upper,
                    nonzero_remainders)) {
                throw std::runtime_error(
                    "finest parent exceeds the 128-bit square-sum safety bound");
            }
        }
    }
    return {
        std::move(parents),
        {depth, lower, upper, parent_count, nonzero_remainders},
        total,
    };
}

void write_raw(const std::string &path, const std::vector<std::uint64_t> &values) {
    std::ofstream output(path, std::ios::binary | std::ios::trunc);
    if (!output) {
        throw std::runtime_error("cannot open coarse output");
    }
    const auto byte_count = static_cast<std::streamsize>(
        values.size() * sizeof(std::uint64_t));
    output.write(reinterpret_cast<const char *>(values.data()), byte_count);
    if (!output) {
        throw std::runtime_error("failed to write coarse output");
    }
}

}  // namespace

int main(int argc, char **argv) {
    try {
        if (argc != 4) {
            std::cerr << "usage: chi_square_interval_core INPUT.npy K COARSE.raw\n";
            return 2;
        }
        const std::uint16_t endian_probe = 1;
        if (*reinterpret_cast<const unsigned char *>(&endian_probe) != 1) {
            throw std::runtime_error("the helper currently requires a little-endian host");
        }
        const int k = std::stoi(argv[2]);
        if (k < 2 || k > 19) {
            throw std::runtime_error("K must lie between 2 and 19");
        }

        const NpyMetadata npy = read_npy_metadata(argv[1], k);
        FirstPass first = stream_first_depth(npy, k - 1);
        std::vector<std::uint64_t> children = std::move(first.parents);
        const u128 total = first.total;
        std::vector<Row> rows = {first.row};
        int stop_depth = 0;
        for (int depth = k - 2; depth >= 1; --depth) {
            if (children.size() % 3 != 0) {
                throw std::runtime_error("genealogy length is not divisible by three");
            }
            const std::uint64_t parent_count = children.size() / 3;
            std::vector<std::uint64_t> parents(parent_count);

            u128 lower = 0;
            u128 upper = 0;
            std::uint64_t nonzero_remainders = 0;
            bool safe = true;
            for (std::uint64_t r = 0; r < parent_count; ++r) {
                if (!accumulate_parent(
                        children[r],
                        children[parent_count + r],
                        children[2 * parent_count + r],
                        parents[r],
                        lower,
                        upper,
                        nonzero_remainders)) {
                    safe = false;
                    break;
                }
            }
            if (!safe) {
                stop_depth = depth;
                break;
            }
            rows.push_back({depth, lower, upper, parent_count, nonzero_remainders});
            children.swap(parents);
        }

        write_raw(argv[3], children);
        std::cout << "TOTAL\t" << decimal(total) << '\n';
        for (const Row &row : rows) {
            std::cout << "ROW\t" << row.depth << '\t' << decimal(row.lower)
                      << '\t' << decimal(row.upper) << '\t' << row.parent_count
                      << '\t' << row.nonzero_remainders << '\n';
        }
        std::cout << "STOP\t" << stop_depth << '\t' << children.size() << '\n';
        return 0;
    } catch (const std::exception &error) {
        std::cerr << "chi_square_interval_core: " << error.what() << '\n';
        return 1;
    }
}
