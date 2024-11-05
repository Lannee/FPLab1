open import Data.Fin using (Fin ; fromℕ<)
open import Agda.Builtin.Nat as Nat using (Nat ; zero ; suc ; _==_ ; _+_ ; _*_ ; _-_ )
open import Data.Nat using (_%_ ; _≤_ ; NonZero ; _^_ ; _/_; compare ; Ordering ; greater ; less ; equal; _≤ᵇ_)
open import Data.Nat using (_<_ ; _≤_ ; s<s ; z<s)
open import Function using (_$_)
open import Relation.Binary using (DecidableEquality)
open import Data.String.Base using (String)
open import Relation.Nullary using (yes ; no)
open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Agda.Builtin.Int using (Int ; pos ; negsuc)
open import Data.Integer as Int using (∣_∣ ; _+_ ; _-_ ; +_)

module date where

module month where
    
    data Month : Set where
        Jan : Month
        Feb : Month
        Mar : Month
        Apr : Month
        May : Month
        Jun : Month
        Jul : Month
        Aug : Month
        Sep : Month
        Oct : Month
        Nov : Month
        Dec : Month
    
    isLeapYear : Nat → Bool
    isLeapYear year = 
        if year % 4 == 0 then 
            if year % 100 == 0 then
                if year % 400 == 0 then true
                else false
            else true
        else false

    daysInMonth : Month → Nat → Nat
    daysInMonth Jan _ = 31
    daysInMonth Feb y = if isLeapYear y then 29 else 28
    daysInMonth Mar _ = 31
    daysInMonth Apr _ = 30
    daysInMonth May _ = 31
    daysInMonth Jun _ = 30
    daysInMonth Jul _ = 31
    daysInMonth Aug _ = 31
    daysInMonth Sep _ = 30
    daysInMonth Oct _ = 31
    daysInMonth Nov _ = 30
    daysInMonth Dec _ = 31

    nextMonth : Month → Month
    nextMonth Jan = Feb 
    nextMonth Feb = Mar
    nextMonth Mar = Apr
    nextMonth Apr = May
    nextMonth May = Jun
    nextMonth Jun = Jul
    nextMonth Jul = Aug
    nextMonth Aug = Sep
    nextMonth Sep = Oct
    nextMonth Oct = Nov
    nextMonth Nov = Dec
    nextMonth Dec = Jan

    prevMonth : Month → Month
    prevMonth Jan = Dec
    prevMonth Feb = Jan
    prevMonth Mar = Feb
    prevMonth Apr = Mar
    prevMonth May = Apr
    prevMonth Jun = May
    prevMonth Jul = Jun
    prevMonth Aug = Jul
    prevMonth Sep = Aug
    prevMonth Oct = Sep
    prevMonth Nov = Oct
    prevMonth Dec = Nov

    infix 4 _-ℕ_

    _-ℕ_ : Month → Nat → Month
    month -ℕ zero    = month
    month -ℕ (suc n) = (prevMonth month) -ℕ n

    toℕ : Month → Nat
    toℕ Jan = 0
    toℕ Feb = 1
    toℕ Mar = 2
    toℕ Apr = 3
    toℕ May = 4
    toℕ Jun = 5
    toℕ Jul = 6
    toℕ Aug = 7
    toℕ Sep = 8
    toℕ Oct = 9
    toℕ Nov = 10
    toℕ Dec = 11

    _>ᵇ-Month_ : Month → Month → Bool
    m1 >ᵇ-Month m2 = (toℕ m2) ≤ᵇ (toℕ m1)

module day where

    data Day : Set where
        Mon : Day
        Tue : Day
        Wed : Day
        Thu : Day
        Fri : Day
        Sat : Day
        Sun : Day


    _≟_ : DecidableEquality Day
    Mon ≟ Mon = yes refl
    Mon ≟ Tue = no λ()
    Mon ≟ Wed = no λ()
    Mon ≟ Thu = no λ()
    Mon ≟ Fri = no λ()
    Mon ≟ Sat = no λ()
    Mon ≟ Sun = no λ()
    Tue ≟ Mon = no λ()
    Tue ≟ Tue = yes refl
    Tue ≟ Wed = no λ()
    Tue ≟ Thu = no λ() 
    Tue ≟ Fri = no λ()
    Tue ≟ Sat = no λ()
    Tue ≟ Sun = no λ()
    Wed ≟ Mon = no λ()
    Wed ≟ Tue = no λ()
    Wed ≟ Wed = yes refl
    Wed ≟ Thu = no λ()
    Wed ≟ Fri = no λ()
    Wed ≟ Sat = no λ()
    Wed ≟ Sun = no λ()
    Thu ≟ Mon = no λ()
    Thu ≟ Tue = no λ()
    Thu ≟ Wed = no λ()
    Thu ≟ Thu = yes refl
    Thu ≟ Fri = no λ()
    Thu ≟ Sat = no λ()
    Thu ≟ Sun = no λ()
    Fri ≟ Mon = no λ()
    Fri ≟ Tue = no λ()
    Fri ≟ Wed = no λ()
    Fri ≟ Thu = no λ()
    Fri ≟ Fri = yes refl
    Fri ≟ Sat = no λ()
    Fri ≟ Sun = no λ()
    Sat ≟ Mon = no λ()
    Sat ≟ Tue = no λ()
    Sat ≟ Wed = no λ()
    Sat ≟ Thu = no λ()
    Sat ≟ Fri = no λ()
    Sat ≟ Sat = yes refl
    Sat ≟ Sun = no λ()
    Sun ≟ Mon = no λ()
    Sun ≟ Tue = no λ()
    Sun ≟ Wed = no λ()
    Sun ≟ Thu = no λ()
    Sun ≟ Fri = no λ()
    Sun ≟ Sat = no λ()
    Sun ≟ Sun = yes refl


    nextDay : Day → Day
    nextDay Mon = Tue
    nextDay Tue = Wed
    nextDay Wed = Thu
    nextDay Thu = Fri
    nextDay Fri = Sat
    nextDay Sat = Sun
    nextDay Sun = Mon

    prevDay : Day → Day
    prevDay Mon = Sun
    prevDay Tue = Mon
    prevDay Wed = Tue
    prevDay Thu = Wed
    prevDay Fri = Thu
    prevDay Sat = Fri
    prevDay Sun = Sat

    infix 4 _+ℕ_

    _+ℕ_ : Day → Nat → Day
    day +ℕ zero    = day
    day +ℕ (suc n) = (nextDay day) +ℕ n

    infix 4 _-ℕ_

    _-ℕ_ : Day → Nat → Day
    day -ℕ zero    = day
    day -ℕ (suc n) = (prevDay day) -ℕ n

record Date : Set where
    constructor _,_,_
    field
        year : Nat
        month : month.Month
        day : Nat
        
dayOfWeek : Date → day.Day
dayOfWeek (year , month , day) = day.Mon day.+ℕ (day) Nat.+ (13 * ((month.toℕ month) Nat.+ 2) / 5) Nat.+ year Nat.+ (year / 4) Nat.- (year / 100) Nat.+ (year / 400)

_+1M : Date → Date
(year , month.Dec , day) +1M = (suc year , month.Jan , day)
(year , month , day) +1M = (year , month.nextMonth month , day)

_+1D : Date → Date
date@(year , month , day) +1D = 
    if (day == month.daysInMonth month year)
    then record date+1M { day = 0 }
    else record date { day = suc day }
    where 
        date+1M = date +1M

_+-days_ : Date → Nat → Date
date +-days zero = date
date +-days (suc n) = (date +1D) +-days n 

_+-months_ : Date → Nat → Date
date +-months zero = date
date +-months (suc n) = (date +1M) +-months n 

_>ᵇ-Date_ : Date → Date → Bool 
(year1 , month1 , day1) >ᵇ-Date (year2 , month2 , day2) with compare year1 year2
... | greater _ _ = true
... | less _ _ = false
... | equal _  with month1 month.>ᵇ-Month month2
...     | true = true
...     | false with compare day1 day2
...          | greater _ _ = true
...          | _ = false

monthsBetween : Date → Date → Nat
monthsBetween (startYear , startMonth , _) (endYear , endMonth , _) = ∣ + ((endYear Nat.- startYear) * 12) Int.+ (+ month.toℕ endMonth) Int.- (+ month.toℕ startMonth) ∣
