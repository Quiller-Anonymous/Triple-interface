// Numerical feasibility probe for the corrected broad-convolution Route A.
//
// This program is diagnostic only. It uses double-precision FFT arithmetic and does not produce
// proof data. Its output mirrors the four fields of RouteABroadPrimeFourierProgram.

#include <algorithm>
#include <cmath>
#include <complex>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

using Complex = std::complex<double>;

constexpr double kPi = 3.141592653589793238462643383279502884;
constexpr double kTwinPrimeConstant = 0.66016181584686957393;

std::size_t next_power_of_two(std::size_t n) {
  std::size_t result = 1;
  while (result < n) {
    result <<= 1;
  }
  return result;
}

void fft(std::vector<Complex>& values, bool invert) {
  const std::size_t n = values.size();
  for (std::size_t i = 1, j = 0; i < n; ++i) {
    std::size_t bit = n >> 1;
    for (; j & bit; bit >>= 1) {
      j ^= bit;
    }
    j ^= bit;
    if (i < j) {
      std::swap(values[i], values[j]);
    }
  }

  for (std::size_t len = 2; len <= n; len <<= 1) {
    const double angle = 2.0 * kPi / static_cast<double>(len) * (invert ? -1.0 : 1.0);
    const Complex root(std::cos(angle), std::sin(angle));
    for (std::size_t i = 0; i < n; i += len) {
      Complex phase(1.0, 0.0);
      for (std::size_t j = 0; j < len / 2; ++j) {
        const Complex even = values[i + j];
        const Complex odd = values[i + j + len / 2] * phase;
        values[i + j] = even + odd;
        values[i + j + len / 2] = even - odd;
        phase *= root;
      }
    }
  }

  if (invert) {
    for (Complex& value : values) {
      value /= static_cast<double>(n);
    }
  }
}

std::vector<int> smallest_prime_factors(int limit) {
  std::vector<int> spf(limit + 1, 0);
  std::vector<int> primes;
  primes.reserve(static_cast<std::size_t>(limit / std::max(1.0, std::log(limit))));
  for (int n = 2; n <= limit; ++n) {
    if (spf[n] == 0) {
      spf[n] = n;
      primes.push_back(n);
    }
    for (int p : primes) {
      const std::int64_t composite = static_cast<std::int64_t>(p) * n;
      if (composite > limit || p > spf[n]) {
        break;
      }
      spf[static_cast<std::size_t>(composite)] = p;
    }
  }
  return spf;
}

double singular_series(int n, const std::vector<int>& spf) {
  if (n % 2 != 0) {
    return 0.0;
  }
  double sigma = 2.0 * kTwinPrimeConstant;
  int remaining = n;
  while (remaining > 1) {
    const int p = spf[remaining];
    if (p > 2) {
      sigma *= static_cast<double>(p - 1) / static_cast<double>(p - 2);
    }
    while (remaining % p == 0) {
      remaining /= p;
    }
  }
  return sigma;
}

std::int64_t extended_gcd(std::int64_t a, std::int64_t b,
                          std::int64_t& x, std::int64_t& y) {
  if (b == 0) {
    x = 1;
    y = 0;
    return a;
  }
  std::int64_t x1 = 0;
  std::int64_t y1 = 0;
  const std::int64_t g = extended_gcd(b, a % b, x1, y1);
  x = y1;
  y = x1 - (a / b) * y1;
  return g;
}

std::int64_t positive_mod(std::int64_t value, std::int64_t modulus) {
  value %= modulus;
  return value < 0 ? value + modulus : value;
}

std::int64_t modular_inverse(std::int64_t value, std::int64_t modulus) {
  std::int64_t x = 0;
  std::int64_t y = 0;
  const std::int64_t g = extended_gcd(value, modulus, x, y);
  if (g != 1) {
    throw std::runtime_error("modular inverse requested for non-coprime values");
  }
  return positive_mod(x, modulus);
}

std::vector<unsigned char> sampled_major_modes(
    std::size_t x, int exponent, long double delta) {
  const std::int64_t modulus = static_cast<std::int64_t>(x + 1);
  const long double q_real = std::pow(std::log(static_cast<long double>(x)), exponent);
  const std::int64_t q_max = std::max<std::int64_t>(1, std::floor(q_real));
  const std::int64_t d_max =
      std::max<std::int64_t>(0, std::ceil(delta * modulus / static_cast<long double>(x)));
  std::vector<unsigned char> modes(static_cast<std::size_t>(modulus), 0);

  // The sampled inequality is equivalent to |k*q - a*M| <= delta*M/X. Enumerating the
  // small integer discrepancy d avoids an O(Q^2) loop over all reduced fractions a/q.
  for (std::int64_t q = 1; q <= q_max; ++q) {
    const std::int64_t g = std::gcd(q, modulus);
    const std::int64_t reduced_q = q / g;
    const std::int64_t reduced_modulus = modulus / g;
    const std::int64_t inverse = modular_inverse(reduced_q, reduced_modulus);
    for (std::int64_t d = -d_max; d <= d_max; ++d) {
      if (d % g != 0) {
        continue;
      }
      const std::int64_t reduced_d = d / g;
      const std::int64_t k0 = positive_mod(reduced_d * inverse, reduced_modulus);
      for (std::int64_t t = 0; t < g; ++t) {
        const std::int64_t k = k0 + t * reduced_modulus;
        const std::int64_t numerator = k * q - d;
        if (numerator < 0 || numerator % modulus != 0) {
          continue;
        }
        const std::int64_t a = numerator / modulus;
        if (std::gcd(a, q) != 1) {
          continue;
        }
        const long double alpha = static_cast<long double>(k) / modulus;
        const long double center = static_cast<long double>(a) / q;
        const long double width = delta / (static_cast<long double>(q) * x);
        if (std::abs(alpha - center) <=
            width + 64.0L * std::numeric_limits<long double>::epsilon()) {
          modes[static_cast<std::size_t>(k)] = 1;
        }
      }
    }
  }

  // Match RouteABroadPrimeMajorModes.conjugationSymmetricClosure.
  const std::vector<unsigned char> raw = modes;
  for (std::int64_t k = 0; k < modulus; ++k) {
    if (raw[static_cast<std::size_t>(k)] != 0) {
      modes[static_cast<std::size_t>((modulus - k) % modulus)] = 1;
    }
  }
  return modes;
}

std::vector<double> project_modes(const std::vector<double>& values,
                                  const std::vector<unsigned char>& modes,
                                  double& max_imaginary) {
  std::vector<Complex> transformed(values.begin(), values.end());
  fft(transformed, false);
  for (std::size_t k = 0; k < transformed.size(); ++k) {
    if (modes[k] == 0) {
      transformed[k] = 0.0;
    }
  }
  fft(transformed, true);
  std::vector<double> result(values.size());
  max_imaginary = 0.0;
  for (std::size_t i = 0; i < transformed.size(); ++i) {
    result[i] = transformed[i].real();
    max_imaginary = std::max(max_imaginary, std::abs(transformed[i].imag()));
  }
  return result;
}

long double l2_norm(const std::vector<double>& values) {
  long double sum = 0.0L;
  for (double value : values) {
    sum += static_cast<long double>(value) * value;
  }
  return std::sqrt(sum);
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const std::size_t x = argc > 1 ? std::stoull(argv[1]) : 1048575;
    const int exponent = argc > 2 ? std::stoi(argv[2]) : 4;
    const long double delta = argc > 3 ? std::stold(argv[3]) : 1.0L;
    if (x < 4 || (x + 1) != next_power_of_two(x + 1)) {
      throw std::runtime_error("X + 1 must be a power of two for this diagnostic");
    }

    const int limit = static_cast<int>(2 * x);
    std::cerr << "[sieve] limit=" << limit << '\n';
    const std::vector<int> spf = smallest_prime_factors(limit);

    const std::size_t convolution_size = next_power_of_two(4 * x + 1);
    std::cerr << "[convolution] fft_size=" << convolution_size << '\n';
    std::vector<Complex> prime_signal(convolution_size, 0.0);
    for (int n = 2; n <= limit; ++n) {
      if (spf[n] == n) {
        prime_signal[static_cast<std::size_t>(n)] = std::log(static_cast<double>(n));
      }
    }
    fft(prime_signal, false);
    for (Complex& value : prime_signal) {
      value *= value;
    }
    fft(prime_signal, true);

    const std::size_t block_size = x + 1;
    std::vector<double> full(block_size, 0.0);
    std::vector<double> main(block_size, 0.0);
    std::vector<double> error(block_size, 0.0);
    double minimum_main_even = std::numeric_limits<double>::infinity();
    double minimum_full_even = std::numeric_limits<double>::infinity();
    double maximum_convolution_imaginary = 0.0;
    for (std::size_t offset = 0; offset < block_size; ++offset) {
      const int n = static_cast<int>(x + offset);
      maximum_convolution_imaginary = std::max(
          maximum_convolution_imaginary,
          std::abs(prime_signal[static_cast<std::size_t>(n)].imag()));
      const double log_n = std::log(static_cast<double>(n));
      full[offset] = std::max(0.0, prime_signal[static_cast<std::size_t>(n)].real()) /
                     (log_n * log_n);
      main[offset] = singular_series(n, spf) * static_cast<double>(n) /
                     (log_n * log_n);
      error[offset] = full[offset] - main[offset];
      if (n % 2 == 0) {
        minimum_main_even = std::min(minimum_main_even, main[offset]);
        minimum_full_even = std::min(minimum_full_even, full[offset]);
      }
    }
    std::vector<Complex>().swap(prime_signal);

    std::cerr << "[modes] B=" << exponent << " delta=" << static_cast<double>(delta) << '\n';
    const std::vector<unsigned char> modes = sampled_major_modes(x, exponent, delta);
    const std::size_t mode_count =
        std::count(modes.begin(), modes.end(), static_cast<unsigned char>(1));

    double full_projection_imaginary = 0.0;
    double main_projection_imaginary = 0.0;
    const std::vector<double> projected_full =
        project_modes(full, modes, full_projection_imaginary);
    const std::vector<double> projected_main =
        project_modes(main, modes, main_projection_imaginary);

    std::vector<double> projected_error(block_size);
    std::vector<double> complement(block_size);
    double projected_main_lower_even = std::numeric_limits<double>::infinity();
    for (std::size_t offset = 0; offset < block_size; ++offset) {
      projected_error[offset] = projected_full[offset] - projected_main[offset];
      complement[offset] = full[offset] - projected_full[offset];
      if ((x + offset) % 2 == 0) {
        projected_main_lower_even =
            std::min(projected_main_lower_even, projected_main[offset]);
      }
    }

    const long double projected_error_l2 = l2_norm(projected_error);
    const long double complement_l2 = l2_norm(complement);
    const long double error_l2 = l2_norm(error);
    const long double budget_margin =
        projected_main_lower_even - projected_error_l2 - complement_l2;

    std::cout << std::setprecision(17);
    std::cout << "X=" << x << '\n';
    std::cout << "block_size=" << block_size << '\n';
    std::cout << "B=" << exponent << '\n';
    std::cout << "delta=" << static_cast<double>(delta) << '\n';
    std::cout << "mode_count=" << mode_count << '\n';
    std::cout << "mode_fraction=" << static_cast<double>(mode_count) / block_size << '\n';
    std::cout << "minimum_main_even=" << minimum_main_even << '\n';
    std::cout << "minimum_full_even=" << minimum_full_even << '\n';
    std::cout << "raw_error_l2=" << static_cast<double>(error_l2) << '\n';
    std::cout << "projected_main_lower_even=" << projected_main_lower_even << '\n';
    std::cout << "projected_error_l2=" << static_cast<double>(projected_error_l2) << '\n';
    std::cout << "complement_l2=" << static_cast<double>(complement_l2) << '\n';
    std::cout << "budget_margin=" << static_cast<double>(budget_margin) << '\n';
    std::cout << "budget_closes=" << (budget_margin > 0.0L ? "true" : "false") << '\n';
    std::cout << "max_convolution_imaginary=" << maximum_convolution_imaginary << '\n';
    std::cout << "max_full_projection_imaginary=" << full_projection_imaginary << '\n';
    std::cout << "max_main_projection_imaginary=" << main_projection_imaginary << '\n';
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
