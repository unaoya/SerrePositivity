module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeEvaluationSpace
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ConeInput
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}}
  (hEval : ∀ x : D, F2.Compact.PreservesKappaFilteredColimits.{u, max (u + 1) v} κ
    (dgBarCompactProjectiveEvaluationSpaceInfinity R D x))
include hEval

/-- 実評価空間の保存から、同じ代表の全 native Hom 保存を得る。 -/
lemma dgBarCompactHom_preserves_of_evaluation (x : D) :
    F2.Compact.PreservesKappaFilteredColimits.{u, max (u + 1) v} κ
      (dgHomTargetUnderlyingSpaceInfinity R (ProjectiveDGModules R D)
        (dgBarCompactRepresentableProjective R D x)) :=
  (hEval x).of_functorIso (dgBarCompactProjectiveEvaluationSpaceIso R D x).symm

/-- 実評価空間の保存から、同じ代表の全整数 shift の native compact 性を得る。 -/
lemma dgBarCompactRepresentableShift_of_evaluation (x : D) (s : ℤ) :
    dgModuleKappaCompact R D κ
      ((ForgetEnrichment.of (Complex R) (representable R x))⟦s⟧) :=
  dgBarCompactRepresentableShift_of_hom_preserves R D
    (dgBarCompactHom_preserves_of_evaluation R D hEval) x s

variable [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
include hκ

/-- 実評価空間の保存から、κ 未満の sphere-free 基底の native compact 性を得る。 -/
lemma dgBarCompactSphereFree_of_evaluation (i : DGKappaSphereFreeIndex D κ) :
    dgModuleKappaCompact R D κ (dgKappaSphereFreeModule R D i) :=
  dgBarCompactSphereFree_of_hom_preserves R D
    (dgBarCompactHom_preserves_of_evaluation R D hEval) hκ i

/-- 実評価空間の保存を七入力の一般判定へ渡し、全選択代表の compact 性を得る。 -/
lemma dgBarCompactClosedProjective_of_evaluation
    (M : ModuleCategory R D) (hM : dgKappaClosedProjectiveObjects R D κ M) :
    dgModuleKappaCompact R D κ M :=
  dgBarCompactClosedProjective_of_hom_preserves R D
    (dgBarCompactHom_preserves_of_evaluation R D hEval) hκ M hM

/-- 同じ代表系の入力の条件付き組立。評価保存と covers の実証拠は引数に残す。 -/
def dgBarCompactConeInputOfEvaluationPreservation
    (hCovers : ∀ y : (dgModuleDerivedInfinityCategory R D) _⦋0⦌,
      F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ y →
        ∃ M : ModuleCategory R D, dgKappaClosedProjectiveObjects R D κ M ∧
          Nonempty (VertexIso (dgConeModuleDerivedVertex R D M) y)) : DGKappaConeInput R D κ :=
  dgBarCompactConeInput R D κ hκ
    (dgBarCompactHom_preserves_of_evaluation R D hEval) hCovers

end SerrePositivity.InfinityCategories
