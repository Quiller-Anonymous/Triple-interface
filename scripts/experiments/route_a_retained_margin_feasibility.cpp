// Numerical audit for the balanced Vaughan retained-arc margin.
//
// This diagnostic mirrors the exact finite coefficients used by the Lean fixed-center split. It
// is not proof data. The retained integrals are evaluated from convolution coefficients and the
// exact integral of each Fourier mode, avoiding quadrature error.

#include <algorithm>
#include <cmath>
#include <complex>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
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

struct SieveData {
  std::vector<int> smallest_prime_factor;
  std::vector<int> mobius;
  std::vector<int> totient;
  std::vector<int> primes;
};

SieveData linear_sieve(int limit) {
  SieveData data;
  data.smallest_prime_factor.assign(limit + 1, 0);
  data.mobius.assign(limit + 1, 0);
  data.totient.assign(limit + 1, 0);
  data.mobius[1] = 1;
  data.totient[1] = 1;

  for (int n = 2; n <= limit; ++n) {
    if (data.smallest_prime_factor[n] == 0) {
      data.smallest_prime_factor[n] = n;
      data.mobius[n] = -1;
      data.totient[n] = n - 1;
      data.primes.push_back(n);
    }
    for (int p : data.primes) {
      const std::int64_t composite = static_cast<std::int64_t>(p) * n;
      if (composite > limit) {
        break;
      }
      data.smallest_prime_factor[static_cast<std::size_t>(composite)] = p;
      if (n % p == 0) {
        data.mobius[static_cast<std::size_t>(composite)] = 0;
        data.totient[static_cast<std::size_t>(composite)] = data.totient[n] * p;
        break;
      }
      data.mobius[static_cast<std::size_t>(composite)] = -data.mobius[n];
      data.totient[static_cast<std::size_t>(composite)] = data.totient[n] * (p - 1);
    }
  }
  return data;
}

std::vector<double> von_mangoldt_values(int limit, const std::vector<int>& primes) {
  std::vector<double> result(limit + 1, 0.0);
  for (int p : primes) {
    const double log_p = std::log(static_cast<double>(p));
    std::int64_t power = p;
    while (power <= limit) {
      result[static_cast<std::size_t>(power)] = log_p;
      if (power > limit / p) {
        break;
      }
      power *= p;
    }
  }
  return result;
}

std::vector<double> convolve(const std::vector<double>& left,
                             const std::vector<double>& right) {
  const std::size_t result_size = left.size() + right.size() - 1;
  const std::size_t fft_size = next_power_of_two(result_size);
  std::vector<Complex> left_fft(fft_size, 0.0);
  std::vector<Complex> right_fft(fft_size, 0.0);
  for (std::size_t i = 0; i < left.size(); ++i) {
    left_fft[i] = left[i];
  }
  if (left.data() == right.data()) {
    fft(left_fft, false);
    for (Complex& value : left_fft) {
      value *= value;
    }
    fft(left_fft, true);
    std::vector<double> result(result_size);
    for (std::size_t i = 0; i < result_size; ++i) {
      result[i] = left_fft[i].real();
    }
    return result;
  }
  for (std::size_t i = 0; i < right.size(); ++i) {
    right_fft[i] = right[i];
  }
  fft(left_fft, false);
  fft(right_fft, false);
  for (std::size_t i = 0; i < fft_size; ++i) {
    left_fft[i] *= right_fft[i];
  }
  std::vector<Complex>().swap(right_fft);
  fft(left_fft, true);

  std::vector<double> result(result_size);
  for (std::size_t i = 0; i < result_size; ++i) {
    result[i] = left_fft[i].real();
  }
  return result;
}

double symmetric_arc_kernel(std::int64_t frequency, double radius) {
  if (frequency == 0) {
    return 2.0 * radius;
  }
  const double h = static_cast<double>(frequency);
  return std::sin(2.0 * kPi * h * radius) / (kPi * h);
}

double centered_arc_integral(const std::vector<double>& convolution, int center,
                             double radius, bool half_turn) {
  long double total = 0.0L;
  for (std::size_t index = 0; index < convolution.size(); ++index) {
    const std::int64_t frequency = static_cast<std::int64_t>(index) - center;
    const double phase = half_turn && (std::abs(frequency) % 2 == 1) ? -1.0 : 1.0;
    total += static_cast<long double>(convolution[index]) * phase
        * symmetric_arc_kernel(frequency, radius);
  }
  return static_cast<double>(total);
}

double cutoff_two_integral(const std::vector<double>& convolution, int center) {
  const double n = static_cast<double>(center);
  return centered_arc_integral(convolution, center, 1.0 / n, false)
      + centered_arc_integral(convolution, center, 1.0 / (2.0 * n), true);
}

int integer_cube_root(int n) {
  int root = static_cast<int>(std::cbrt(static_cast<double>(n)));
  while (static_cast<std::int64_t>(root + 1) * (root + 1) * (root + 1) <= n) {
    ++root;
  }
  while (static_cast<std::int64_t>(root) * root * root > n) {
    --root;
  }
  return root;
}

double singular_series(int n, const SieveData& sieve) {
  if (n % 2 != 0) {
    return 0.0;
  }
  double result = 2.0 * kTwinPrimeConstant;
  int remaining = n;
  while (remaining > 1) {
    const int p = sieve.smallest_prime_factor[remaining];
    if (p > 2) {
      result *= static_cast<double>(p - 1) / static_cast<double>(p - 2);
    }
    while (remaining % p == 0) {
      remaining /= p;
    }
  }
  return result;
}

double active_discrete_main(int lower, int center, int cutoff, const SieveData& sieve) {
  const int upper_y = center - lower;
  long double total = 0.0L;
  for (int d = 1; d <= cutoff; ++d) {
    if (sieve.mobius[d] == 0 || std::gcd(d, center) != 1) {
      continue;
    }
    const int lower_y = std::max(lower, d);
    if (lower_y > upper_y) {
      continue;
    }
    long double inner = 0.0L;
    const int first_quotient = lower_y / d;
    const int last_quotient = upper_y / d;
    for (int quotient = first_quotient; quotient <= last_quotient; ++quotient) {
      const int block_lower = std::max(lower_y, quotient * d);
      const int block_upper = std::min(upper_y, (quotient + 1) * d - 1);
      if (quotient > 0 && block_lower <= block_upper) {
        inner += static_cast<long double>(block_upper - block_lower + 1)
            * std::log(static_cast<double>(quotient));
      }
    }
    total += static_cast<long double>(sieve.mobius[d]) / sieve.totient[d] * inner;
  }
  return static_cast<double>(total);
}

double active_continuous_main(int lower, int center, int cutoff, const SieveData& sieve) {
  const double upper_y = static_cast<double>(center - lower);
  long double total = 0.0L;
  for (int d = 1; d <= cutoff; ++d) {
    if (sieve.mobius[d] == 0 || std::gcd(d, center) != 1) {
      continue;
    }
    const double lower_y = static_cast<double>(std::max(lower, d));
    if (lower_y > upper_y) {
      continue;
    }
    const auto antiderivative = [d](double y) {
      return y * (std::log(y / static_cast<double>(d)) - 1.0);
    };
    const double inner = antiderivative(upper_y) - antiderivative(lower_y);
    total += static_cast<long double>(sieve.mobius[d]) / sieve.totient[d] * inner;
  }
  return static_cast<double>(total);
}

void print_ratio(const std::string& name, double value, int center) {
  std::cout << name << "=" << value << "\n";
  std::cout << name << "_over_N=" << value / static_cast<double>(center) << "\n";
}

}  // namespace

int main(int argc, char** argv) {
  try {
    const int center = argc > 1 ? std::stoi(argv[1]) : 1048576;
    const int lower = argc > 2 ? std::stoi(argv[2]) : 2;
    const int cutoff = argc > 3 ? std::stoi(argv[3]) : integer_cube_root(center);
    if (center < 4 || center % 2 != 0) {
      throw std::runtime_error("N must be an even integer at least four");
    }
    if (lower < 1 || 2 * lower > center) {
      throw std::runtime_error("L must be positive and satisfy 2L <= N");
    }
    if (cutoff < 1 || cutoff > center) {
      throw std::runtime_error("u must lie in [1,N]");
    }

    std::cerr << "[sieve] N=" << center << " L=" << lower << " u=" << cutoff << '\n';
    const SieveData sieve = linear_sieve(center);
    std::vector<double> lambda = von_mangoldt_values(center, sieve.primes);
    std::vector<double> type_i(center + 1, 0.0);
    std::vector<double> geometric(center + 1, 0.0);

    const int upper = center - lower;
    for (int n = lower; n <= upper; ++n) {
      geometric[n] = 1.0;
      if (lambda[n] == 0.0) {
        continue;
      }
    }
    for (int n = 0; n < lower; ++n) {
      lambda[n] = 0.0;
    }
    for (int n = upper + 1; n <= center; ++n) {
      lambda[n] = 0.0;
    }

    for (int d = 1; d <= cutoff; ++d) {
      const int mu = sieve.mobius[d];
      if (mu == 0) {
        continue;
      }
      const int first_r = (lower + d - 1) / d;
      const int last_r = upper / d;
      for (int r = std::max(1, first_r); r <= last_r; ++r) {
        type_i[d * r] += mu * std::log(static_cast<double>(r));
      }
    }

    std::cerr << "[convolution] Lambda*Lambda\n";
    std::vector<double> lambda_lambda = convolve(lambda, lambda);
    const double full_lambda_lambda = lambda_lambda[center];
    const double retained_lambda_lambda = cutoff_two_integral(lambda_lambda, center);
    std::vector<double>().swap(lambda_lambda);

    std::cerr << "[convolution] TypeI*Lambda\n";
    std::vector<double> type_i_lambda = convolve(type_i, lambda);
    const double full_type_i_lambda = type_i_lambda[center];
    const double retained_type_i_lambda = cutoff_two_integral(type_i_lambda, center);
    std::vector<double>().swap(type_i_lambda);

    std::cerr << "[convolution] geometric*geometric\n";
    std::vector<double> geometric_geometric = convolve(geometric, geometric);
    const double actual_retained_geometric = cutoff_two_integral(geometric_geometric, center);
    const double geometric_q1 = centered_arc_integral(
        geometric_geometric, center, 1.0 / static_cast<double>(center), false);
    const double geometric_q2_model = centered_arc_integral(
        geometric_geometric, center, 1.0 / (2.0 * center), false);
    const double cutoff_two_geometric_model = geometric_q1 + geometric_q2_model;
    std::vector<double>().swap(geometric_geometric);

    std::cerr << "[convolution] TypeI*geometric models\n";
    std::vector<double> type_i_geometric = convolve(type_i, geometric);
    const double model_q1 = centered_arc_integral(
        type_i_geometric, center, 1.0 / static_cast<double>(center), false);
    std::vector<double>().swap(type_i_geometric);

    std::vector<double> alternating_type_i = type_i;
    for (int n = 1; n <= center; n += 2) {
      alternating_type_i[n] = -alternating_type_i[n];
    }
    std::vector<double> alternating_type_i_geometric = convolve(alternating_type_i, geometric);
    const double model_q2 = -centered_arc_integral(
        alternating_type_i_geometric, center, 1.0 / (2.0 * center), false);
    std::vector<double>().swap(alternating_type_i_geometric);

    const double retained_type_i_model = model_q1 + model_q2;
    const double discrete_main = active_discrete_main(lower, center, cutoff, sieve);
    const double continuous_main = active_continuous_main(lower, center, cutoff, sieve);
    const double full_hard = full_lambda_lambda - full_type_i_lambda;
    const double retained_hard = retained_lambda_lambda - retained_type_i_lambda;
    const double complement_lambda_lambda = full_lambda_lambda - retained_lambda_lambda;
    const double complement_type_i = full_type_i_lambda - retained_type_i_lambda;
    const double complement_hard = full_hard - retained_hard;
    const double support_size = static_cast<double>(upper - lower + 1);
    double minimum_type_i = type_i[lower];
    std::size_t negative_type_i_count = 0;
    for (int n = lower; n <= upper; ++n) {
      minimum_type_i = std::min(minimum_type_i, type_i[n]);
      if (type_i[n] < 0.0) {
        ++negative_type_i_count;
      }
    }
    const double type_i_q1_density =
        std::accumulate(type_i.begin(), type_i.end(), 0.0) / support_size;
    long double alternating_type_i_sum = 0.0L;
    for (int n = lower; n <= upper; ++n) {
      alternating_type_i_sum += (n % 2 == 0 ? 1.0L : -1.0L) * type_i[n];
    }
    const double type_i_q2_density =
        -static_cast<double>(alternating_type_i_sum) / support_size;

    if (center <= 4096) {
      long double direct_lambda_lambda = 0.0L;
      long double direct_type_i_lambda = 0.0L;
      for (int n = lower; n <= upper; ++n) {
        direct_lambda_lambda += static_cast<long double>(lambda[n]) * lambda[center - n];
        direct_type_i_lambda += static_cast<long double>(type_i[n]) * lambda[center - n];
      }
      const double scale = std::max(1.0, std::abs(full_lambda_lambda));
      if (std::abs(static_cast<double>(direct_lambda_lambda) - full_lambda_lambda)
              > 1.0e-9 * scale
          || std::abs(static_cast<double>(direct_type_i_lambda) - full_type_i_lambda)
              > 1.0e-9 * scale) {
        throw std::runtime_error("FFT convolution failed the direct small-N check");
      }
    }

    std::cout << std::setprecision(17);
    std::cout << "N=" << center << "\nL=" << lower << "\nu=" << cutoff << '\n';
    std::cout << "singular_series=" << singular_series(center, sieve) << '\n';
    std::cout << "minimum_type_i_weight=" << minimum_type_i << '\n';
    std::cout << "negative_type_i_weight_count=" << negative_type_i_count << '\n';
    std::cout << "type_i_q1_density=" << type_i_q1_density << '\n';
    std::cout << "type_i_q2_density=" << type_i_q2_density << '\n';
    print_ratio("active_discrete_main", discrete_main, center);
    print_ratio("active_continuous_main", continuous_main, center);
    print_ratio("full_lambda_lambda", full_lambda_lambda, center);
    print_ratio("full_type_i_lambda", full_type_i_lambda, center);
    print_ratio("retained_lambda_lambda", retained_lambda_lambda, center);
    print_ratio("retained_type_i_lambda", retained_type_i_lambda, center);
    print_ratio("actual_retained_geometric", actual_retained_geometric, center);
    print_ratio("cutoff_two_geometric_model", cutoff_two_geometric_model, center);
    print_ratio("type_i_model_q1", model_q1, center);
    print_ratio("type_i_model_q2", model_q2, center);
    print_ratio("retained_type_i_model", retained_type_i_model, center);
    print_ratio("retained_pair_difference",
                retained_lambda_lambda - retained_type_i_lambda, center);
    print_ratio("complement_lambda_lambda", complement_lambda_lambda, center);
    print_ratio("complement_type_i", complement_type_i, center);
    print_ratio("full_hard", full_hard, center);
    print_ratio("retained_hard", retained_hard, center);
    print_ratio("complement_hard", complement_hard, center);
    print_ratio("recombined_main_model",
                discrete_main + retained_lambda_lambda - retained_type_i_model, center);
    return EXIT_SUCCESS;
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return EXIT_FAILURE;
  }
}
