module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGHomTargetUnit
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
/-!
概要：実 Hom 単位による全 Hom の比較鎖写像は、同じ dg Yoneda 同型の逆そのもの。
方針：全次数で評価し、実閉単位の回収と共変 representable の符号付き作用を使う。
規約：入力の射影性も対象の小ささも不要。使われ方：coslice の全 fiber 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] (x y : C)
/-- 同じ Hom 単位の閉 cycle を Yoneda 評価へ戻すと、元の単位 cycle。 -/
lemma dgHomTargetUnit_cycle_evaluation :
    (dgYonedaIso R PUnit.unit ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj x)).hom.f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnit R C x))).val =
    (_root_.SerrePositivity.DifferentialGraded.unitElement R x).val := by
  have h := congrArg (fun f ↦ (cycleFromUnit _ f).val) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnit_evaluation R C x)
  rw [_root_.SerrePositivity.DifferentialGraded.cycleFromUnit_postcomp] at h
  exact h
/-- 実 Hom 鎖写像と同じ単位前合成を Yoneda 評価で戻すと恒等鎖写像。 -/
lemma dgHomTargetUnitHomComparison :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).map x y ≫
      eHomWhiskerRight (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnit R C x)
        (ForgetEnrichment.of (Complex R) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj y)) ≫
      (dgYonedaIso R PUnit.unit ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj y)).hom = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (dgYonedaIso R PUnit.unit ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj y)).hom.f k
    ((eHomWhiskerRight (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnit R C x)
      (ForgetEnrichment.of (Complex R) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj y))).f k
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).map x y).f k f)) = f
  rw [show (dgYonedaIso R PUnit.unit ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj y)).hom =
    yonedaEvaluateFamily R PUnit.unit ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj y)
      (fun z ↦ _root_.SerrePositivity.DifferentialGraded.moduleHomπ R PUnit.{1} (_root_.SerrePositivity.DifferentialGraded.representable R PUnit.unit)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj y) z.unop) from rfl]
  rw [_root_.SerrePositivity.DifferentialGraded.yonedaEvaluateFamily_apply]
  erw [_root_.SerrePositivity.DifferentialGraded.moduleHomWhiskerRight_apply_π]
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  have hm : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).map x y ≫
      moduleHomπ R PUnit.{1} ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj x)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj y) PUnit.unit =
      (_root_.SerrePositivity.DifferentialGraded.leftRepresentable R x).map x y := by
    change ((_root_.SerrePositivity.DifferentialGraded.leftRepresentable R x).map x y ≫
      (_root_.SerrePositivity.DifferentialGraded.ringConstantHomIso R _ _).inv) ≫ (_root_.SerrePositivity.DifferentialGraded.ringConstantHomIso R _ _).hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hv := congrArg (fun a ↦ a.f k f) hm
  have ht := dgHomTargetUnit_cycle_evaluation R C x
  rw [show (dgYonedaIso R PUnit.unit ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj x)).hom =
    yonedaEvaluateFamily R PUnit.unit ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj x)
      (fun z ↦ _root_.SerrePositivity.DifferentialGraded.moduleHomπ R PUnit.{1} (_root_.SerrePositivity.DifferentialGraded.representable R PUnit.unit)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj x) z.unop) from rfl,
    _root_.SerrePositivity.DifferentialGraded.yonedaEvaluateFamily_apply] at ht
  erw [← _root_.SerrePositivity.DifferentialGraded.moduleEvaluation_cochain] at ht
  simp only [Cochain.ofHom_v] at ht
  change ((moduleHomπ R PUnit.{1} ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj x)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj y) PUnit.unit).f k
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).map x y).f k f)).v 0 k (zero_add k)
    (((moduleEvaluation R PUnit.{1} PUnit.unit).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnit R C x)).f 0
      (_root_.SerrePositivity.DifferentialGraded.unitElement R PUnit.unit).val) = f
  change (moduleHomπ R PUnit.{1} ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj x)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj y) PUnit.unit).f k
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).map x y).f k f) =
      ((_root_.SerrePositivity.DifferentialGraded.leftRepresentable R x).map x y).f k f at hv
  rw [hv]
  change _root_.SerrePositivity.DifferentialGraded.leftAction R (_root_.SerrePositivity.DifferentialGraded.leftRepresentable R x) f
    (((moduleEvaluation R PUnit.{1} PUnit.unit).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnit R C x)).f 0
      (_root_.SerrePositivity.DifferentialGraded.unitElement R PUnit.unit).val) (zero_add k) = f
  erw [ht, _root_.SerrePositivity.DifferentialGraded.leftRepresentable_action]
  simp only [mul_zero, Int.negOnePow_zero, one_smul, _root_.SerrePositivity.DifferentialGraded.forward_unit]
/-- 同じ実比較鎖写像は、同じ全 Hom の dg Yoneda 同型の逆に等しい。 -/
lemma dgHomTargetUnitHomMap_eq :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).map x y ≫
      eHomWhiskerRight (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnit R C x)
        (ForgetEnrichment.of (Complex R) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj y)) =
    (dgYonedaIso R PUnit.unit ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj y)).inv := by
  apply (cancel_mono (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R PUnit.unit
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj y)).hom).mp
  rw [Category.assoc, dgHomTargetUnitHomComparison, Iso.inv_hom_id]
/-- 同じ実 Hom 比較鎖写像は全次数の鎖同型。 -/
lemma dgHomTargetUnitHomMap_isIso :
    IsIso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).map x y ≫
      eHomWhiskerRight (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnit R C x)
        (ForgetEnrichment.of (Complex R) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R C x).obj y))) := by
  rw [dgHomTargetUnitHomMap_eq]
  infer_instance
end SerrePositivity.InfinityCategories.Project.DerivedCategories
