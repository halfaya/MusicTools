abbrev Pitch  := Int
abbrev Octave := Int
def PC := {n : Int // 0 ≤ n ∧ n < 12}

def PCOctave : Type := PC × Octave

def absoluteToRelative (p : Pitch) : PCOctave :=
  ⟨⟨p % 12,
     And.intro (Int.emod_nonneg p (by simp))
               (Int.emod_lt_of_pos p (by simp))⟩,
   p / 12⟩

def relativeToAbsolute : PCOctave → Pitch
  | ⟨p , o⟩ => o * 12 + p.1

theorem PitchToPCOctaveToPitch (p: Pitch) :
     relativeToAbsolute (absoluteToRelative p) = p :=
   Int.ediv_add_emod' p 12

theorem PCOctaveToPitchToPCOctave : (pco: PCOctave) →
    absoluteToRelative (relativeToAbsolute pco) = pco := by
  intro pco
  unfold relativeToAbsolute absoluteToRelative;
  rw [← Prod.eta pco]
  apply Prod.ext_iff.2; simp
  constructor

  apply Subtype.ext; simp
  rw [Int.add_emod, Int.mul_emod_left]; simp
  rw [Int.emod_eq_of_lt pco.fst.property.1 pco.fst.property.2]

  rw [Int.add_ediv_of_dvd_left (Int.dvd_mul_left pco.snd 12)]
  rw [Int.mul_ediv_cancel pco.snd (by simp)]
  rw [Int.ediv_eq_zero_of_lt pco.fst.property.1 pco.fst.property.2]
  simp

instance : Coe Pitch PCOctave where
  coe := absoluteToRelative

def pitchClass : PCOctave → PC
  | (p, _) => p
