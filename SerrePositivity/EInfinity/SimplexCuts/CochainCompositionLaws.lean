module

public import SerrePositivity.EInfinity.SimplexCuts.CochainCompositionInput
public import SerrePositivity.EInfinity.SimplexCuts.NullaryActionLaw

/-!
# BF切断余作用の全arityの元の複体射の合成則

Berger–Fresse §1.2.4・§2.2.6、M14 L14/L16、報告 §388。
元の基底値の等式を二つの語基底と全正規化単体の外延性で延長する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

/-- L16：空語を含む全arityで元の実複体射の部分合成則（BF §2.2.6）。 -/
lemma coaction_comp_all (A : Type u) [CommRing A] (S : SSet.{0}) (m n : ℕ) (k : Fin (m + 1)) :
    (Surjection.complexPartialComposition A m n k ▷ chains A S) ≫ cochainAction A S (m + n) =
      iteratedCochainAction A S m n k := by
  apply coefficient_simplex_hom_ext A S (m + 1) n
  intro d e q u v x
  exact (cochainAction_composition_input A S u v k x).trans
    (cochainAction_composition_basis_eq_iterated_all A S u v k x _ rfl)

/-- L14：空語を代入する場合も元の同じ実複体射の合成則（BF §2.2.6）。 -/
lemma coaction_comp_nullary (A : Type u) [CommRing A] (S : SSet.{0}) (m : ℕ) (k : Fin (m + 1)) :
    (Surjection.complexPartialComposition A m 0 k ▷ chains A S) ≫ cochainAction A S m =
      iteratedCochainAction A S m 0 k :=
  coaction_comp_all A S m 0 k

end SerrePositivity.EInfinity.SimplexCuts
