module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DegreeOneShiftHomology
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.SignedShiftBlockValues
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Algebra

/-!
概要：符号つき一次 shift ブロックのホモロジー射を元の閉零射へ同定する。
方針：実次数成分の符号相殺を cycle の shift 輸送へ適用する。
規約：元の閉零 Hom 要素から作る実加群射を使う。
使われ方：実一次ホモロジー複体と通常の bar の各係数の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {M N : ModuleCategory R D}
  (f : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
    (ForgetEnrichment.to (Complex R) N)).X 0)
  (hf : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
    (ForgetEnrichment.to (Complex R) N)).d 0 1 f = 0)

def dgBarSignedShiftCochain (n : ℤ) (x : D) :
    Cochain (((moduleEvaluation R D x).obj M)⟦n + 1⟧)
      (((moduleEvaluation R D x).obj N)⟦n⟧) 1 :=
  (n + 1).negOnePow •
    (_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D (shiftModule (n + 1) (ForgetEnrichment.to (Complex R) M))
      (shiftModule n (ForgetEnrichment.to (Complex R) N)) x).f 1
        (moduleHomShiftBlock R D (n + 1) n f (by omega))

include hf in
lemma dgBarSignedShiftCochain_closed (n : ℤ) (x : D) :
    δ 1 2 (dgBarSignedShiftCochain R D f n x) = 0 := by
  have hb : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (shiftModule (n + 1) (ForgetEnrichment.to (Complex R) M))
      (shiftModule n (ForgetEnrichment.to (Complex R) N))).d 1 2
        (moduleHomShiftBlock R D (n + 1) n f (by omega)) = 0 := by
    erw [_root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlock_d R D (n + 1) n f (by omega), hf]
    simp only [moduleHomShiftBlock, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero]
  have he := _root_.SerrePositivity.DifferentialGraded.moduleHomElement_d_π R D 1 2
    (moduleHomShiftBlock R D (n + 1) n f (by omega)) x
  rw [hb, map_zero] at he
  rw [dgBarSignedShiftCochain, δ_units_smul, he.symm, smul_zero]

lemma dgBarSignedShiftHomology (n q : ℤ) (x : D) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap R (dgBarSignedShiftCochain R D f n x)
      (dgBarSignedShiftCochain_closed R D f hf n x) q ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso R ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).obj N) n
        (q + 1) (q + (n + 1)) (by omega)).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso R ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).obj M) (n + 1)
      q (q + (n + 1)) (by omega)).hom ≫
      HomologicalComplex.homologyMap
        ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map (moduleMorphismOfCycle R D f hf)) (q + (n + 1)) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap_shift R _ n q (q + (n + 1)) (by omega)
  dsimp only [dgBarSignedShiftCochain]
  erw [Cochain.units_smul_v, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarSignedShiftBlock_v]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id, Category.comp_id]
  have h := moduleEvaluation_cochain R D x (moduleMorphismOfCycle R D f hf)
  rw [moduleMorphismOfCycle_cycle] at h
  rw [← h, Cochain.ofHom_v]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
