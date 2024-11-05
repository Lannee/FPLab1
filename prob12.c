#include <stdint.h>
#include <stddef.h>

size_t number_of_divisors(uint64_t n) {
    size_t divisors = 0;
    for (size_t i = 1; i <= n ; i++) {
        if (n % i == 0) divisors++;
    }
    return divisors;
}

uint64_t find_tringular_number(size_t divisors) {
    uint64_t tr_num = 1;
    size_t i = 1;
    while (number_of_divisors(tr_num) < divisors) {
        if (tr_num > UINT64_MAX - ++i) return -1;
        tr_num += i;
    }
    return tr_num;
}