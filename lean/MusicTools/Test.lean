inductive ℕ : Type where
  | zero : ℕ
  | succ : ℕ → ℕ

def add : ℕ → ℕ → ℕ
  | m, ℕ.zero   => m
  | m, ℕ.succ n => ℕ.succ (add m n)

theorem add_zero (m : Nat) : m + 0 = m := rfl

--theorem zero_add_bad (m : Nat) : 0 + m = m := rfl

theorem zero_add (m : Nat) : 0 + m = m := by
  induction m with
  | zero => rfl
  | succ m ih => rewrite [Nat.add_succ, ih]; rfl

  #eval Lean.versionString
