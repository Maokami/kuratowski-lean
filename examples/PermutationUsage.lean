import Kuratowski.PermSum

/-! The permutation API can be imported without graph or planarity modules. -/

open Equiv Kuratowski

example {α β : Type*} [Finite α] [Finite β] (f : Perm α) (g : Perm β) :
    orbitCount (Perm.sumCongr f g) = orbitCount f + orbitCount g :=
  orbitCount_sumCongr f g

example {α β : Type*} (f : Perm α) (g : Perm β) (n : ℕ) (a : α) :
    ((Perm.sumCongr f g) ^ n) (.inl a) = .inl ((f ^ n) a) :=
  pow_sumCongr_inl f g n a
