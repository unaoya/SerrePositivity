module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.EndRebaseAlgebra
/-!
概要：同じ graded 成分を保つ実 MC Hom への移送は単射である。
方針：全評価 cochain の各成分で等式を判定する。
規約：微分変更前後の要素を成分で比較し、微分の一致は仮定しない。
使われ方：実鎖写像の閉性を元の全 Hom 上の twisted 方程式へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarEndRebase_injective (q : ℤ) :
    Function.Injective (dgCoherentBarEndRebase R D F hMC q) := by
  intro z w h
  apply moduleHomElement_ext R D
    (M := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (N := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
  intro x
  apply Cochain.ext
  intro i j hij
  have he := congrArg (fun a => Cochain.v
    ((moduleHomπ R D (dgCoherentBarModule R D F hMC)
      (dgCoherentBarModule R D F hMC) x).f q a) i j hij) h
  rw [dgCoherentBarEndRebase_π, dgCoherentBarEndRebase_π] at he
  exact he

end SerrePositivity.InfinityCategories
