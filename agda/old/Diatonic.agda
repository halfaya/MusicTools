{-# OPTIONS --cubical --safe #-}

module Diatonic where

open import Prelude renaming (_+_ to _+ℕ_)
open import Data.Integer using (_+_)

open import Interval            using (Upi; maj3; min3)
open import Pitch               using (Pitch; s7; PC; pitchToClass)
open import Util                using (_∘_)

data Mode : Set where
  major : Mode
  minor : Mode

DiatonicDegree : Set
DiatonicDegree = Fin s7

infix 4 _≡ᵈ_
_≡ᵈ_ : DiatonicDegree → DiatonicDegree → Bool
d ≡ᵈ e = toℕ d == toℕ e
-- round down
pitchClass→Degree : Mode → PC → DiatonicDegree

pitchClass→Degree major (fz)                                                        = # 0
pitchClass→Degree major ((fs fz))                                                   = # 0
pitchClass→Degree major ((fs (fs fz)))                                              = # 1
pitchClass→Degree major ((fs (fs (fs fz))))                                         = # 1
pitchClass→Degree major ((fs (fs (fs (fs fz)))))                                    = # 2
pitchClass→Degree major ((fs (fs (fs (fs (fs fz))))))                               = # 3
pitchClass→Degree major ((fs (fs (fs (fs (fs (fs fz)))))))                          = # 3
pitchClass→Degree major ((fs (fs (fs (fs (fs (fs (fs fz))))))))                     = # 4
pitchClass→Degree major ((fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))                = # 4
pitchClass→Degree major ((fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))))           = # 5
pitchClass→Degree major ((fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))))      = # 5
pitchClass→Degree major ((fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))))) = # 6

pitchClass→Degree minor (fz)                                                        = # 0
pitchClass→Degree minor ((fs fz))                                                   = # 0
pitchClass→Degree minor ((fs (fs fz)))                                              = # 1
pitchClass→Degree minor ((fs (fs (fs fz))))                                         = # 2
pitchClass→Degree minor ((fs (fs (fs (fs fz)))))                                    = # 2
pitchClass→Degree minor ((fs (fs (fs (fs (fs fz))))))                               = # 3
pitchClass→Degree minor ((fs (fs (fs (fs (fs (fs fz)))))))                          = # 3
pitchClass→Degree minor ((fs (fs (fs (fs (fs (fs (fs fz))))))))                     = # 4
pitchClass→Degree minor ((fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))                = # 5
pitchClass→Degree minor ((fs (fs (fs (fs (fs (fs (fs (fs (fs fz))))))))))           = # 5
pitchClass→Degree minor ((fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))))      = # 6
pitchClass→Degree minor ((fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs fz)))))))))))) = # 6

degree→PC : Mode → DiatonicDegree → PC

degree→PC major fz                               = (# 0)
degree→PC major (fs fz)                          = (# 2)
degree→PC major (fs (fs fz))                     = (# 4)
degree→PC major (fs (fs (fs fz)))                = (# 5)
degree→PC major (fs (fs (fs (fs fz))))           = (# 7)
degree→PC major (fs (fs (fs (fs (fs fz)))))      = (# 9)
degree→PC major (fs (fs (fs (fs (fs (fs fz)))))) = (# 11)

degree→PC minor fz                               = (# 0)
degree→PC minor (fs fz)                          = (# 2)
degree→PC minor (fs (fs fz))                     = (# 3)
degree→PC minor (fs (fs (fs fz)))                = (# 5)
degree→PC minor (fs (fs (fs (fs fz))))           = (# 7)
degree→PC minor (fs (fs (fs (fs (fs fz)))))      = (# 8)
degree→PC minor (fs (fs (fs (fs (fs (fs fz)))))) = (# 10)

pitch→DegreeCMajor : Pitch → DiatonicDegree
pitch→DegreeCMajor = pitchClass→Degree major ∘ pitchToClass

d1 d2 d3 d4 d5 d6 d7 : DiatonicDegree
d1 = # 0
d2 = # 1
d3 = # 2
d4 = # 3
d5 = # 4
d6 = # 5
d7 = # 6

data Accidental : Set where
  ♭3 : ℕ → Accidental -- 3+n flats
  𝄫  : Accidental
  ♭  : Accidental
  ♮  : Accidental
  ♯  : Accidental
  𝄪  : Accidental
  ♯3 : ℕ → Accidental -- 3+n sharps

-- pitch class letter name with accidental
data PCL : Set where
  A : Accidental → PCL
  B : Accidental → PCL
  C : Accidental → PCL
  D : Accidental → PCL
  E : Accidental → PCL
  F : Accidental → PCL
  G : Accidental → PCL

-- Accidental modifier.
accMod : Accidental → ℤ
accMod (♭3 n) = -[1+ (n +ℕ 2) ]
accMod 𝄫      = -[1+ 1 ]
accMod ♭      = -[1+ 0 ]
accMod ♮      = + 0
accMod ♯      = + 1
accMod 𝄪      = + 2
accMod (♯3 n) = + (n +ℕ 3)

flatten : (a : Accidental) → Accidental
flatten (♭3 n)       = ♭3 (suc n)
flatten 𝄫            = ♭3 zero
flatten ♭            = 𝄫
flatten ♮            = ♭
flatten ♯            = ♮
flatten 𝄪            = ♯
flatten (♯3 zero)    = 𝄪
flatten (♯3 (suc n)) = ♯3 n

sharpen : Accidental → Accidental
sharpen (♭3 (suc n)) = ♭3 n
sharpen (♭3 zero)    = 𝄫
sharpen 𝄫            = ♭
sharpen ♭            = ♮
sharpen ♮            = ♯
sharpen ♯            = 𝄪
sharpen 𝄪            = ♯3 zero
sharpen (♯3 n)       = ♯3 (suc n)

-- Convert raw PCL letter to ℕ (in range [0,11]); C normalized to 0
letter→ℕ : PCL → ℕ
letter→ℕ (A _) = 9
letter→ℕ (B _) = 11
letter→ℕ (C _) = 0
letter→ℕ (D _) = 2
letter→ℕ (E _) = 4
letter→ℕ (F _) = 5
letter→ℕ (G _) = 7

accidental : PCL → Accidental
accidental (A x) = x
accidental (B x) = x
accidental (C x) = x
accidental (D x) = x
accidental (E x) = x
accidental (F x) = x
accidental (G x) = x

modifyAccidental : (Accidental → Accidental) → PCL →  PCL
modifyAccidental f (A x) = A (f x)
modifyAccidental f (B x) = B (f x)
modifyAccidental f (C x) = C (f x)
modifyAccidental f (D x) = D (f x)
modifyAccidental f (E x) = E (f x)
modifyAccidental f (F x) = F (f x)
modifyAccidental f (G x) = G (f x)

-- Convert PCL to PC with C♮ normalized to 0.
pclToC : PCL → PC
pclToC pc = ((((+ (letter→ℕ pc)) + accMod (accidental pc)) modℕ 12) mod 12)

data Key : Set where
  key : PCL → Mode → Key

keyMode : Key → Mode
keyMode (key _ mode) = mode

data Step : Set where
  half  : Step
  whole : Step

stepUp : Step → PCL → PCL

stepUp half  (A x) = B (flatten x)
stepUp half  (B x) = C x
stepUp half  (C x) = D (flatten x)
stepUp half  (D x) = E (flatten x)
stepUp half  (E x) = F x
stepUp half  (F x) = G (flatten x)
stepUp half  (G x) = A (flatten x)

stepUp whole (A x) = B x
stepUp whole (B x) = C (sharpen x)
stepUp whole (C x) = D x
stepUp whole (D x) = E x
stepUp whole (E x) = F (sharpen x)
stepUp whole (F x) = G x
stepUp whole (G x) = A x

scaleSteps : Mode → Vec Step s7
scaleSteps major = whole ∷ whole ∷ half ∷ whole ∷ whole ∷ whole ∷ half ∷ []
scaleSteps minor = whole ∷ half ∷ whole ∷ whole ∷ half ∷ whole ∷ whole ∷ []

scaleNotes : Key → Vec PCL s7
scaleNotes (key pc m) =
  let f : {n : ℕ} → Vec PCL (suc n) → Step → Vec PCL (suc (suc n))
      f pcs step = stepUp step (head pcs) ∷ pcs
  in vreverse (foldl (Vec PCL ∘ suc) f (pc ∷ []) (take 6 (scaleSteps m)))

data Root : Set where
  I   : Root
  II  : Root
  III : Root
  IV  : Root
  V   : Root
  VI  : Root
  VII : Root

data Quality : Set where
  maj : Quality
  min : Quality
  aug : Quality
  dim : Quality

_dd+_ : DiatonicDegree → ℕ → DiatonicDegree
d dd+ n = (toℕ d +ℕ n) mod s7

thirdUp : DiatonicDegree → DiatonicDegree
thirdUp d = d dd+ 2

data Triad : Set where
  triad : Root → Quality → Triad

root→DiatonicDegree : Root → DiatonicDegree
root→DiatonicDegree I   = d1
root→DiatonicDegree II  = d2
root→DiatonicDegree III = d3
root→DiatonicDegree IV  = d4
root→DiatonicDegree V   = d5
root→DiatonicDegree VI  = d6
root→DiatonicDegree VII = d7

diatonicDegree→Root : DiatonicDegree → Root
diatonicDegree→Root fz                               = I
diatonicDegree→Root (fs fz)                          = II
diatonicDegree→Root (fs (fs fz))                     = III
diatonicDegree→Root (fs (fs (fs fz)))                = IV
diatonicDegree→Root (fs (fs (fs (fs fz))))           = V
diatonicDegree→Root (fs (fs (fs (fs (fs fz)))))      = VI
diatonicDegree→Root (fs (fs (fs (fs (fs (fs fz)))))) = VII

rootQuality : Mode → Root → Quality

rootQuality major I   = maj
rootQuality major II  = min
rootQuality major III = min
rootQuality major IV  = maj
rootQuality major V   = maj
rootQuality major VI  = min
rootQuality major VII = dim

rootQuality minor I   = min
rootQuality minor II  = dim
rootQuality minor III = maj
rootQuality minor IV  = min
rootQuality minor V   = min
rootQuality minor VI  = maj
rootQuality minor VII = maj

root→PC : Key → Root → PC
root→PC (key _ mode) = degree→PC mode ∘ root→DiatonicDegree

diatonicDegree→PCL : Key → DiatonicDegree → PCL
diatonicDegree→PCL k dd = lookup (scaleNotes k) dd

root→PCL : Key → Root → PCL
root→PCL k = diatonicDegree→PCL k ∘ root→DiatonicDegree

-- Lower interval is first.
triadQuality : Upi → Upi → Quality
triadQuality i1 i2 =
  if      (i1 == maj3) ∧ (i2 == min3) then maj
  else if (i1 == min3) ∧ (i2 == maj3) then min
  else if (i1 == min3) ∧ (i2 == min3) then dim
  else if (i1 == maj3) ∧ (i2 == maj3) then aug
  else maj -- should not happen

makeTriad : Mode → Root → Triad
makeTriad m r =
  let d1 = root→DiatonicDegree r
      d2 = thirdUp d1
      d3 = thirdUp d2
      p1 = degree→PC m d1
      p2 = degree→PC m d2
      p3 = degree→PC m d3
      i1 = toℕ p2 ∸ toℕ p1 -- TODO: See if want to use ℤ
      i2 = toℕ p3 ∸ toℕ p2
  in triad r (triadQuality i1 i2)

diatonic7thNotes : Key → Root → Vec PCL 4
diatonic7thNotes k root =
  let d1 = root→DiatonicDegree root
      d2 = thirdUp d1
      d3 = thirdUp d2
      d4 = thirdUp d3
      ns = scaleNotes k
  in lookup ns d1 ∷ lookup ns d2 ∷ lookup ns d3 ∷ lookup ns d4 ∷ []

triadNotes : Key → Root → Vec PCL 3
triadNotes k = take 3 ∘ diatonic7thNotes k

_V/_ : Key → Root → Vec PCL 3
k V/ r = triadNotes (key (root→PCL k r) major) V

_V⁷/_ : Key → Root → Vec PCL 4
k V⁷/ r = diatonic7thNotes (key (root→PCL k r) major) V

_viiᵒ⁷/_ : Key → Root → Vec PCL 4
k viiᵒ⁷/ r = updateAt (# 3) (modifyAccidental flatten) (diatonic7thNotes (key (root→PCL k r) major) VII)

----------

a1 = triadNotes (key (G ♭) major) III
a2 = diatonic7thNotes (key (G ♯) major) V
a3 = diatonic7thNotes (key (E ♮) major) V
a4 = diatonic7thNotes (key (B ♭) major) VI
a5 = scaleNotes (key (G ♯) major)
a6 = scaleNotes (key (G ♭) major)
a7 = scaleNotes (key (B ♮) minor)
a8 = (key (G ♮) major) V/ V
a9 = (key (B ♭) major) V⁷/ II

a10 = (key (F ♯) minor) viiᵒ⁷/ III
