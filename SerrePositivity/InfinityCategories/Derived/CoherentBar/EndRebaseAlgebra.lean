module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.EndRebase
/-!
概要：実 MC bar への次数付き自己 Hom の移送は零・単位・斉次合成を保つ。
方針：元の全評価 cochain の成分を保持することと、実 Hom 合成の成分公式を使う。
規約：鎖写像性を主張するのではなく、微分変更下で同じ graded 代数を保持する。
使われ方：実正規化の有限段階と、元の単体列上の計算の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open HomologicalComplex CochainComplex HomComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarEndRebase_zero (q : ℤ) :
    dgCoherentBarEndRebase R D F hMC q 0 = 0 := by
  apply moduleHomElement_ext R D
  intro x
  rw [map_zero]
  apply Cochain.ext
  intro i j hij
  rw [dgCoherentBarEndRebase_π, map_zero]
  rfl

lemma dgCoherentBarEndRebase_unit :
    dgCoherentBarEndRebase R D F hMC 0
      (unitElement R (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).val =
      (unitElement R (dgCoherentBarModule R D F hMC)).val := by
  apply moduleHomElement_ext R D
  intro x
  apply Cochain.ext
  intro i j hij
  rw [dgCoherentBarEndRebase_π, yoneda_moduleUnit_π, yoneda_moduleUnit_π]
  obtain rfl : j = i := by omega
  rfl

lemma dgCoherentBarEndRebase_compose {p q k : ℤ}
    (f : (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X p)
    (g : (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X q) (hk : p + q = k) :
    compose R (x := dgCoherentBarModule R D F hMC) (y := dgCoherentBarModule R D F hMC)
      (z := dgCoherentBarModule R D F hMC)
      (dgCoherentBarEndRebase R D F hMC q g) (dgCoherentBarEndRebase R D F hMC p f) hk =
    dgCoherentBarEndRebase R D F hMC k
      (compose R (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) g f hk) := by
  apply moduleHomElement_ext R D
  intro x
  rw [moduleHomCompose_π]
  apply Cochain.ext
  intro i j hij
  rw [dgCoherentBarEndRebase_π, moduleHomCompose_π]
  rw [Cochain.comp_v _ _ hk i (i + p) j rfl (by omega),
    Cochain.comp_v _ _ hk i (i + p) j rfl (by omega)]
  rw [dgCoherentBarEndRebase_π, dgCoherentBarEndRebase_π]


lemma dgCoherentBarEndRebase_sub (q : ℤ)
    (z w : (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X q) :
    dgCoherentBarEndRebase R D F hMC q (z - w) =
      dgCoherentBarEndRebase R D F hMC q z - dgCoherentBarEndRebase R D F hMC q w := by
  apply moduleHomElement_ext R D
  intro x
  simp only [map_sub, dgCoherentBarEndRebase, moduleHomElementMk_π]
  apply Cochain.ext
  intro i j hij
  rfl

end SerrePositivity.InfinityCategories
