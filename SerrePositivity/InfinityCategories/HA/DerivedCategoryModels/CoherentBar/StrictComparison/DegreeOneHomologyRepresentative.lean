module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DegreeOneHomologyMap

/-!
概要：閉じた次数一作用素によるホモロジー射の cycle 代表元公式。
方針：隣接短複体との比較と、cycle の核普遍性を使う。
規約：元の作用素による実 cycle の像を保持する。
使われ方：実 bar の連結射と一次作用素のホモロジー射の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] {K L : Complex R}
  (z : Cochain K L 1) (hz : δ 1 2 z = 0)

lemma dgDegreeOneHomologyMap_representative (q : ℤ) :
    K.homologyπ q ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap R z hz q =
      L.liftCycles (K.iCycles q ≫ z.v q (q + 1) rfl) (q + 2)
        (by apply ComplexShape.next_eq'; change (q + 1) + 1 = q + 2; omega)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneCochain_cycles_closed R z hz q) ≫ L.homologyπ (q + 1) := by
  let f := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneShortComplexMap R z hz q
  let c := L.liftCycles (K.iCycles q ≫ z.v q (q + 1) rfl) (q + 2)
    (by apply ComplexShape.next_eq'; change (q + 1) + 1 = q + 2; omega)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneCochain_cycles_closed R z hz q)
  have hc : (K.cyclesIsoSc' (q - 1) q (q + 1) (by simp) (by simp)).hom ≫
      ShortComplex.cyclesMap f ≫
        (L.cyclesIsoSc' q (q + 1) (q + 2) (by simp) (by simp; omega)).inv = c := by
    rw [← cancel_mono (L.iCycles (q + 1))]
    simp only [Category.assoc, HomologicalComplex.cyclesIsoSc'_inv_iCycles,
      ShortComplex.cyclesMap_i, HomologicalComplex.cyclesIsoSc'_hom_iCycles_assoc,
      c, HomologicalComplex.liftCycles_i]
    rfl
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap]
  rw [← Category.assoc, HomologicalComplex.π_homologyIsoSc'_hom, Category.assoc,
    ShortComplex.homologyπ_naturality_assoc,
    HomologicalComplex.π_homologyIsoSc'_inv]
  simpa only [Category.assoc] using congrArg (fun a => a ≫ L.homologyπ (q + 1)) hc

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
