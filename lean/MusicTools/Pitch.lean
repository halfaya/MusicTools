notation "Octave" => Int
notation "Pitch" => Int
def PC := {n : Int // 0 ≤ n ∧ n < 12}

instance : Coe Pitch Int where
  coe p := p

def PCOctave : Type := PC × Octave

def absoluteToRelative (p : Pitch) : PCOctave :=
  ⟨⟨p % 12,
     And.intro (Int.emod_nonneg p (by simp))
               (Int.emod_lt_of_pos p (by simp))⟩,
   p / 12⟩

def relativeToAbsolute : PCOctave → Pitch
  | ⟨p , o⟩ => o * 12 + p.1

/-
def relativeToAbsolute (po : PitchOctave) : Pitch :=
  po.2 * 12 + po.1
-/

theorem PitchToPCOctaveToPitch (p: Pitch) :
   relativeToAbsolute (absoluteToRelative p) = p :=
   Int.ediv_add_emod' p 12

theorem PCOctaveToPitchToPCOctave :
  (pco: PCOctave) → absoluteToRelative (relativeToAbsolute pco) = pco := by
  intro pco
  unfold relativeToAbsolute absoluteToRelative;
  rw [← Prod.eta pco]
  apply Prod.ext_iff.2
  simp
  constructor

  apply Subtype.ext
  simp
  rw [Int.add_emod]
  rw [Int.mul_emod_left]
  rw [Int.emod_eq_of_lt pco.fst.property.1 pco.fst.property.2]
  simp

  rw [Int.add_ediv_of_dvd_left (Int.dvd_mul_left pco.snd 12)]
  let x : (12: Int) ≠ 0 := by simp
  rw [Int.mul_ediv_cancel pco.snd x]
  rw [Int.ediv_eq_zero_of_lt pco.fst.property.1 pco.fst.property.2]
  simp
