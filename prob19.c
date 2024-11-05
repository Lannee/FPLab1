#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

typedef enum {
    JANUARY = 0,
    FEBRUARY,
    MARCH,
    APRIL,
    MAY,
    JUNE,
    JULY,
    AUGUST,
    SEPTEMBER,
    OCTOBER,
    NOVEMBER,
    DECEMBER
} Month;

typedef enum {
    MONDAY = 0,
    TUESDAY,
    WEDNESDAY,
    THURSDAY,
    FRIDAY,
    SATURDAY,
    SUNDAY
} DayOfWeek;

DayOfWeek day_of_week(uint64_t year, Month month, uint8_t day) {
    return (day + (13 * (month + 1) / 5) + year + (year / 4) - (year / 100) + (year / 400) + 1) % 7;
}

bool is_leap_year(uint64_t year) {
    return (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0);
}

size_t days_in_month(Month month, uint64_t year) {
    switch (month) {
        case APRIL:
        case JUNE:
        case SEPTEMBER:
        case NOVEMBER:
            return 30;
        case 2:
            return is_leap_year(year) ? 29 : 28;
        default:
            return 31;
    }
}

size_t calculate_sundays() {
    size_t sundays = 0;
    for (size_t year = 1901; year <= 2000; year++) {
        for (Month month = JANUARY; month <= DECEMBER; month++) {
            if (day_of_week(year, month, 1) == SUNDAY) sundays++;
        }
    }
    return sundays;
}