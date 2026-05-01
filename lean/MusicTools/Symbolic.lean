namespace Symbolic

inductive Letter : Type where
| A : Letter
| B : Letter
| C : Letter
| D : Letter
| E : Letter
| F : Letter
| G : Letter
deriving Repr

def letterToString (ℓ : Letter) : String :=
  String.Slice.copy (String.takeEnd (toString (repr ℓ)) 1)

instance : ToString Letter := ⟨ letterToString ⟩

inductive Acc : Type where
| «𝄫» : Acc
| «♭» : Acc
| «♮» : Acc
| «♯» : Acc
| «𝄪» : Acc
deriving Repr

def accToString (a : Acc) : String :=
  String.Slice.copy
    (String.Slice.takeEnd
      (String.dropEnd (toString (repr a)) 1)
      1)

instance : ToString Acc := ⟨ accToString ⟩

structure NoteName where
  ltr : Letter
  acc : Acc
deriving Repr

def noteNameToString : NoteName → String
| ⟨ l , a ⟩ => toString l ++ toString a

instance : ToString NoteName := ⟨ noteNameToString ⟩

abbrev Octave := Int

structure SPitch where
  nam : NoteName
  oct : Octave
deriving Repr

#eval toString (⟨ Letter.D , Acc.«𝄫» ⟩ : NoteName)
