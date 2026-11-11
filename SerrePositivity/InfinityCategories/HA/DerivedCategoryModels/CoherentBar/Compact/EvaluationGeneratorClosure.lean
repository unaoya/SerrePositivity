module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeEvaluationSpace
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.ConeInput
/-!
概要：実評価空間の全 native 余極限保存を、代表系の七入力と K-7 入力へ接続する。
方針：全 Hom―評価の全関手同型を通し、検証済みの生成元閉性と組立を再利用する。
規約：評価保存と covers は明示入力。coherent C1 を証明したとは主張しない。
使われ方：C1 と covers の実値が供給された後の D-8 c6・c7 の代入入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}}
  (hEval : ∀ x : D, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, max (u + 1) v} κ
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x))
include hEval

/-- 実評価空間の保存から、同じ代表の全 native Hom 保存を得る。 -/
lemma dgBarCompactHom_preserves_of_evaluation (x : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, max (u + 1) v} κ
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetUnderlyingSpaceInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactRepresentableProjective R D x)) :=
  (hEval x).of_functorIso (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceIso R D x).symm

/-- 実評価空間の保存から、同じ代表の全整数 shift の native compact 性を得る。 -/
lemma dgBarCompactRepresentableShift_of_evaluation (x : D) (s : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ
      ((ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.representable R x))⟦s⟧) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactRepresentableShift_of_hom_preserves R D
    (dgBarCompactHom_preserves_of_evaluation R D hEval) x s

variable [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
include hκ

/-- 実評価空間の保存から、κ 未満の sphere-free 基底の native compact 性を得る。 -/
lemma dgBarCompactSphereFree_of_evaluation (i : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeModule R D i) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactSphereFree_of_hom_preserves R D
    (dgBarCompactHom_preserves_of_evaluation R D hEval) hκ i

/-- 実評価空間の保存を七入力の一般判定へ渡し、全選択代表の compact 性を得る。 -/
lemma dgBarCompactClosedProjective_of_evaluation
    (M : ModuleCategory R D) (hM : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ M :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactClosedProjective_of_hom_preserves R D
    (dgBarCompactHom_preserves_of_evaluation R D hEval) hκ M hM

/-- 同じ代表系の入力の条件付き組立。評価保存と covers の実証拠は引数に残す。 -/
def dgBarCompactConeInputOfEvaluationPreservation
    (hCovers : ∀ y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, max (u + 1) v} κ y →
        ∃ M : ModuleCategory R D, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ M ∧
          Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (dgConeModuleDerivedVertex R D M) y)) : DGKappaConeInput R D κ :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactConeInput R D κ hκ
    (dgBarCompactHom_preserves_of_evaluation R D hEval) hCovers

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
