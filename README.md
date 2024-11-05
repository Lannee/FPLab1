# Функциональное программирование
## Лабораторная работа №1


- Выполнил : Булко Егор Олегович P3306
- Вариант : 12 , 19

## Задачи

### Problem 12
>
> The sequence of triangle numbers is generated by adding the natural numbers.
>
> What is the value of the first triangle number to have over five hundred divisors?  

Суть задачи заключается в нахождении числа делителей для каждого треугольного числа и выбрать то, у которго первым число делителей превысит 500

### Problem 12 Solution
___Далее приведены различные варианты реализации функции подсчета числа делителей___

1) Монолитная реализация

- С использованием рекурсии

```agda
numberOfDivisorsRecursive : Nat → Nat
numberOfDivisorsRecursive zero = zero
numberOfDivisorsRecursive n@(suc _) with flooredSqrt n
... | zero = zero
... | sqrtn@(suc _) = 2 * inner n sqrtn - (if n % sqrtn == 0 then 1 else 0)
    where 
        inner : (n : Nat) {{_ : NonZero n}} → Nat → Nat
        inner n zero = zero
        inner n div@(suc div-1) = (if n % div == 0 then 1 else 0) + inner n div-1
```

- С использованием хвостовой рекурсии
```agda
numberOfDivisorsTailRecursive : Nat → Nat
numberOfDivisorsTailRecursive zero = zero
numberOfDivisorsTailRecursive n@(suc _) with flooredSqrt n
... | zero = zero
... | sqrtn@(suc _) = 2 * inner n sqrtn 0 - (if n % sqrtn == 0 then 1 else 0)
    where 
        inner : (n : Nat) {{_ : NonZero n}} → Nat → Nat → Nat
        inner n zero acc = acc
        inner n div@(suc div-1) acc = inner n div-1 $ acc + (if n % div == 0 then 1 else 0)
```

2) Модульная реализация (с использованием функций filter и fold)
```agda
numberOfDivisorsFilter : Nat → Nat
numberOfDivisorsFilter n with flooredSqrt n
... | zero = zero
... | sqrtn@(suc _) = (λ e → 2 * e - (if n % sqrtn == 0 then 1 else 0)) $
    foldl (λ acc _ → suc acc) 0 $ filterᵇ (λ {zero → false ; x@(suc _) → n % x == 0}) $ range (suc sqrtn)
```

3) Генерация с использованием отображения (map)
```agda
numberOfDivisorsMap : Nat → Nat
numberOfDivisorsMap n with flooredSqrt n
... | zero = zero
... | sqrtn@(suc _) = (λ e → 2 * e - (if n % sqrtn == 0 then 1 else 0)) $
    List.sum $ List.map (λ {zero → 0 ; x@(suc _) → if n % x == zero then 1 else 0}) $ range (suc sqrtn)
```

4) Генерация с использованием бесконечной последовательности (Stream)
```agda
numberOfDivisorsStream : Nat → Nat
numberOfDivisorsStream n with flooredSqrt n
... | zero = zero
... | sqrtn@(suc _) = (λ e → 2 * e - (if n % sqrtn == 0 then 1 else 0)) $
    Vec.sum $ Vec.map (λ {zero → 0 ; x@(suc _) → if n % x == zero then 1 else 0}) $ take (suc sqrtn) $ iterate suc 0
```

___Функция находящая треугольное число с количеством делителей первышающим 500___

```agda
findTringularNumber : (Nat → Nat) → Nat → Nat
findTringularNumber countDivisors divisors = go 1 2
    where
        go : Nat → Nat → Nat
        go prevTriag nextInd = if divisors < countDivisors newTriag then newTriag else go newTriag (suc nextInd)
            where
                newTriag : Nat
                newTriag = prevTriag + nextInd
```

Реализация на языке программирования C
```C
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
```

### Problem 19
>
> - Thirty days has September,
>   April, June and November.
>   All the rest have thirty-one,
>   Saving February alone,
>   Which has twenty-eight, rain or shine.
>   And on leap years, twenty-nine.
> - A leap year occurs on any year evenly divisible by 4, but not on a century unless it is divisible by 400.
>
> How many Sundays fell on the first of the month during the twentieth century (1 Jan 1901 to 31 Dec 2000)? 

Задача сводится к перебору каждого первого числа месяца и подсчету количества тех, что являются Воскресеньями  

### Problem 19 Solution
1) Монолитная реализация

- С использованием рекурсии

```agda
recursiveAlgorithm : Nat
recursiveAlgorithm = recursiveAlgorithmHelper 1Jan1901 31Dec2000
    where    
        recursiveAlgorithmHelper : Date → Date → Nat
        recursiveAlgorithmHelper start@(_ , _ , startDay) end = 
            if start >ᵇ-Date end 
            then 0
            else if (isSunday $ dayOfWeek start) ∧ (startDay == 1)
                then 1 + recursiveAlgorithmHelper (start +1D) end
                else recursiveAlgorithmHelper (start +1D) end
```

- С использованием хвостовой рекурсии
```agda
tailRecursiveAlgorithm : Nat
tailRecursiveAlgorithm = tailRecursiveAlgorithmHelper 1Jan1901 31Dec2000 0
    where
        tailRecursiveAlgorithmHelper : Date → Date → Nat → Nat
        tailRecursiveAlgorithmHelper start@(_ , _ , startDay) end acc = 
            if start >ᵇ-Date end 
            then acc
            else if (isSunday $ dayOfWeek start) ∧ (startDay == 1)
                then tailRecursiveAlgorithmHelper (start +1D) end (suc acc)
                else tailRecursiveAlgorithmHelper (start +1D) end acc
```

2) Модульная реализация использующая бесконечную последовательность (с использованием filter, fold и Stream)
```agda
streamAlgorithm : Nat
streamAlgorithm = 
    foldl′ (λ acc _ → suc acc) 0                                   $ 
    Data.Vec.Bounded.Base.Vec≤.vec                                 $ 
    filter (λ e → dayOfWeek e day.≟ day.Sun)                       $ 
    take (monthsBetween 1Jan1901 31Dec2000) (iterate _+1M 1Jan1901)
```

3) Генерация с использованием отображения (map)
```agda
mapAlgorithm : Nat
mapAlgorithm = sum $ Vec.map (λ e → if isSunday $ dayOfWeek e then 1 else 0) $ Vec.map (λ m → 1Jan1901 +-months toℕ m) $ allFin $ monthsBetween 1Jan1901 31Dec2000
```

Реализация на языке программирования C
```C
DayOfWeek day_of_week(uint64_t year, Month month, uint8_t day) {
    return (day + (13 * (month + 1) / 5) + year + (year / 4) - (year / 100) + (year / 400) + 1) % 7;
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
```

## Вывод
1) Обе задачи сочетаю в себе такие действия, как создания послендовательности, анализ ее элементов, изменение ее элементов и итоговая свертка
2) Основным преимуществом классического языка оказалось большая гибкость в отлаживании
3) Преимуществани использавния функционального языка программирования оказалась сильная система типов
3) Активная фиксация на функциях и их композициях позволили задать правила обработки более плотным синтаксисом
4) Поиск треугольного числа с использованием бесконечной последоваетльности не удалось реализовать ввиду прагматичности agda в отслеживании завершаемости программы