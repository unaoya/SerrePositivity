module

public import SerrePositivity.CategoryTheory.FiniteBijectionAction
public import SerrePositivity.CategoryTheory.Monoidal.PermutationAction

/-!
# 有限全単射圏上の反復テンソル関手

全次数の置換作用を、小さい有限全単射圏上の一つの関手にまとめる。
一般の対称モノイダル圏の構成であり、スペクトルや円には依存しない。
-/

@[expose] public section

universe v u

noncomputable section

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 有限集合の濃度を反復テンソルへ、全単射を置換作用へ送る関手。 -/
def bijectionFunctor (X : C) : FiniteBijection ⥤ C :=
  FiniteBijection.familyFunctor (power X) (permutationAction X)

/-- 標準のn元集合での値は第n段の反復テンソル。 -/
lemma bijectionFunctor_obj_of (X : C) (n : ℕ) :
    (bijectionFunctor X).obj (FiniteBijection.of n) = power X n := rfl

/-- 標準の置換での値は構成した置換作用。 -/
lemma bijectionFunctor_map_permutation (X : C) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (bijectionFunctor X).map (FiniteBijection.permutation n σ) =
      (permutationAction X n σ).asIso.hom :=
  FiniteBijection.familyFunctor_map_permutation (power X) (permutationAction X) n σ

end SerrePositivity.TensorPowers
