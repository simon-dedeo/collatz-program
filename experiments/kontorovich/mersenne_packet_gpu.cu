#include <cuda_runtime.h>

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <limits>
#include <string>
#include <vector>

struct Hit {
  unsigned long long initial_h;
  unsigned char length;
  unsigned char extras[8];
};

__device__ unsigned long long d_hit_count;
__device__ unsigned long long d_overflow_count;
__device__ unsigned int d_max_length;

__global__ void scan_packets(unsigned long long begin_index,
                             unsigned long long count,
                             unsigned int max_steps,
                             unsigned int threshold,
                             Hit* hits,
                             unsigned long long hit_capacity) {
  const unsigned long long local =
      static_cast<unsigned long long>(blockIdx.x) * blockDim.x + threadIdx.x;
  if (local >= count) return;
  const unsigned long long initial_h = 2 * (begin_index + local) + 1;
  unsigned long long h = initial_h;
  unsigned long long power_three = 3;
  unsigned char extras[8] = {};
  unsigned int length = 0;

  for (unsigned int offset = 0; offset < max_steps; ++offset) {
    const unsigned int level = 1 + offset;
    if (h > (~0ULL) / power_three) {
      atomicAdd(&d_overflow_count, 1ULL);
      break;
    }
    const unsigned long long raw = power_three * h - 1;
    const unsigned int extra = __ffsll(static_cast<long long>(raw)) - 1;
    const unsigned long long endpoint = raw >> extra;
    if (endpoint == ~0ULL) {
      atomicAdd(&d_overflow_count, 1ULL);
      break;
    }
    const unsigned long long shifted = endpoint + 1;
    const unsigned int next_level = level + 1;
    const unsigned long long mask = (1ULL << next_level) - 1;
    if ((shifted & mask) != 0) break;
    const unsigned long long next_h = shifted >> next_level;
    if ((next_h & 1ULL) == 0) break;
    extras[length] = static_cast<unsigned char>(extra);
    ++length;
    h = next_h;
    power_three *= 3;
  }

  atomicMax(&d_max_length, length);
  if (length >= threshold) {
    const unsigned long long slot = atomicAdd(&d_hit_count, 1ULL);
    if (slot < hit_capacity) {
      hits[slot].initial_h = initial_h;
      hits[slot].length = static_cast<unsigned char>(length);
      for (unsigned int i = 0; i < max_steps; ++i) {
        hits[slot].extras[i] = extras[i];
      }
    }
  }
}

static void check_cuda(cudaError_t status, const char* what) {
  if (status != cudaSuccess) {
    std::cerr << what << ": " << cudaGetErrorString(status) << "\n";
    std::exit(2);
  }
}

int main(int argc, char** argv) {
  unsigned int h_bits = 36;
  unsigned int max_steps = 8;
  unsigned int threshold = 6;
  std::string output = "mersenne_packet_gpu_results.json";
  for (int i = 1; i < argc; ++i) {
    if (!std::strcmp(argv[i], "--h-bits") && i + 1 < argc) {
      h_bits = static_cast<unsigned int>(std::stoul(argv[++i]));
    } else if (!std::strcmp(argv[i], "--max-steps") && i + 1 < argc) {
      max_steps = static_cast<unsigned int>(std::stoul(argv[++i]));
    } else if (!std::strcmp(argv[i], "--threshold") && i + 1 < argc) {
      threshold = static_cast<unsigned int>(std::stoul(argv[++i]));
    } else if (!std::strcmp(argv[i], "--output") && i + 1 < argc) {
      output = argv[++i];
    } else {
      std::cerr << "unknown or incomplete argument: " << argv[i] << "\n";
      return 2;
    }
  }
  if (h_bits < 2 || h_bits > 62 || max_steps < 1 || max_steps > 8 ||
      threshold < 1 || threshold > max_steps) {
    std::cerr << "invalid bounds\n";
    return 2;
  }

  const unsigned long long odd_candidates = 1ULL << (h_bits - 1);
  constexpr unsigned long long hit_capacity = 1000000ULL;
  Hit* device_hits = nullptr;
  check_cuda(cudaMalloc(&device_hits, hit_capacity * sizeof(Hit)), "cudaMalloc");
  const unsigned long long zero64 = 0;
  const unsigned int zero32 = 0;
  check_cuda(cudaMemcpyToSymbol(d_hit_count, &zero64, sizeof(zero64)),
             "reset hit count");
  check_cuda(cudaMemcpyToSymbol(d_overflow_count, &zero64, sizeof(zero64)),
             "reset overflow count");
  check_cuda(cudaMemcpyToSymbol(d_max_length, &zero32, sizeof(zero32)),
             "reset maximum");

  cudaDeviceProp properties{};
  check_cuda(cudaGetDeviceProperties(&properties, 0), "device properties");
  const unsigned int threads = 256;
  const unsigned long long chunk = 1ULL << 30;
  for (unsigned long long begin = 0; begin < odd_candidates; begin += chunk) {
    const unsigned long long count =
        (odd_candidates - begin < chunk) ? odd_candidates - begin : chunk;
    const unsigned int blocks = static_cast<unsigned int>((count + threads - 1) / threads);
    scan_packets<<<blocks, threads>>>(begin, count, max_steps, threshold,
                                      device_hits, hit_capacity);
    check_cuda(cudaGetLastError(), "kernel launch");
    check_cuda(cudaDeviceSynchronize(), "kernel completion");
    std::cerr << "processed " << (begin + count) << " / " << odd_candidates
              << " odd packets\n";
  }

  unsigned long long hit_count = 0;
  unsigned long long overflow_count = 0;
  unsigned int maximum = 0;
  check_cuda(cudaMemcpyFromSymbol(&hit_count, d_hit_count, sizeof(hit_count)),
             "copy hit count");
  check_cuda(cudaMemcpyFromSymbol(&overflow_count, d_overflow_count,
                                  sizeof(overflow_count)),
             "copy overflow count");
  check_cuda(cudaMemcpyFromSymbol(&maximum, d_max_length, sizeof(maximum)),
             "copy maximum");
  if (hit_count > hit_capacity) {
    std::cerr << "hit capacity exceeded: " << hit_count << "\n";
    return 3;
  }
  std::vector<Hit> hits(hit_count);
  if (hit_count) {
    check_cuda(cudaMemcpy(hits.data(), device_hits, hit_count * sizeof(Hit),
                          cudaMemcpyDeviceToHost),
               "copy hits");
  }
  check_cuda(cudaFree(device_hits), "cudaFree");

  std::ofstream out(output);
  if (!out) {
    std::cerr << "cannot open output " << output << "\n";
    return 2;
  }
  out << "{\n"
      << "  \"schema\": \"collatz-mersenne-packet-gpu-search-v1\",\n"
      << "  \"arithmetic\": \"exact_uint64_with_overflow_counter\",\n"
      << "  \"device\": \"" << properties.name << "\",\n"
      << "  \"bounds\": {\"start_level\": 1, \"odd_h_less_than\": \""
      << (1ULL << h_bits) << "\", \"h_bits\": " << h_bits
      << ", \"max_steps\": " << max_steps << ", \"threshold\": "
      << threshold << "},\n"
      << "  \"odd_packets_checked\": \"" << odd_candidates << "\",\n"
      << "  \"overflow_count\": \"" << overflow_count << "\",\n"
      << "  \"maximum_renewals\": " << maximum << ",\n"
      << "  \"hits_at_or_above_threshold\": \"" << hit_count << "\",\n"
      << "  \"hits\": [\n";
  for (unsigned long long i = 0; i < hit_count; ++i) {
    out << "    {\"initial_h\": \"" << hits[i].initial_h
        << "\", \"renewals\": " << static_cast<unsigned int>(hits[i].length)
        << ", \"extras\": [";
    for (unsigned int j = 0; j < hits[i].length; ++j) {
      if (j) out << ", ";
      out << static_cast<unsigned int>(hits[i].extras[j]);
    }
    out << "]}" << (i + 1 == hit_count ? "\n" : ",\n");
  }
  out << "  ]\n}\n";
  out.close();
  std::cout << "wrote " << output << "; max=" << maximum
            << "; hits=" << hit_count << "; overflows=" << overflow_count
            << "\n";
  return overflow_count == 0 ? 0 : 4;
}
