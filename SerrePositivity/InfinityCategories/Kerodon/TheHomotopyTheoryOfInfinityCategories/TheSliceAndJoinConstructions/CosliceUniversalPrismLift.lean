module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceUniversalPrism
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationRelativeParameterLifting

/-!
概要：coslice 全体の標準区間族を、指定した fiber の点から同時に持ち上げる。
方針：零端点と恒等錐上の定値族を貼り、left anodyne の相対持ち上げを使う。
規約：始点と恒等錐上の区間全体を厳密に保つ。底の充填性を要求しない。
使われ方：大域比較の同じ始点を保つ輸送表示と、全対象上の一意性への接続。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 指定始点と恒等錐上の定値区間を同時に保つ、普遍 coslice 区間族の持ち上げ。 -/
lemma exists_cosliceUniversalPrism_lift {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (b : B _⦋0⦌) (d : E _⦋0⦌)
    (hd : p.app (Opposite.op ⦋0⦌) d = b) :
    ∃ W : (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm b) ⟶ E,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ W = SSet.const d ∧
      (Δ[1] ◁ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone b)) ≫ W = SSet.const d ∧
      W ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceUniversalPrism b := by
  let A := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm b)
  let j : (Δ[0] : SSet.{u}) ⟶ A := SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone b)
  have : Mono j := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    rw [mono_iff_injective]
    intro x y _
    apply stdSimplex.ext
    intro i
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  have hv : (SSet.const d : (Δ[0] : SSet.{u}) ⊗ A ⟶ E) ≫ p =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1 ▷ A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceUniversalPrism b := by
    rw [SSet.const_comp, hd, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight]
    change SSet.const b = snd (Δ[0] : SSet.{u}) A ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceUniversalPrism b
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceUniversalPrism_zero, SSet.comp_const]
  obtain ⟨W, hWj, hW₀, hWp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibration_lift_relative_parameters p
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex_leftAnodyne 1) j
    (SSet.const d) (SSet.const d) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceUniversalPrism b)
    (by simp only [SSet.comp_const])
    (by rw [SSet.const_comp, hd]; exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceUniversalPrism_identity b).symm) hv
  refine ⟨W, ?_, hWj, hWp⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.scaffoldFirstVertex_whiskerRight] at hW₀
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  exact congrArg (fun f ↦ f.app n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n.unop.len,
    x)) hW₀

/-- 同じ二つの固定条件を持つ普遍 coslice 区間族の持ち上げを選ぶ。 -/
def cosliceUniversalPrismLift {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (b : B _⦋0⦌) (d : E _⦋0⦌)
    (hd : p.app (Opposite.op ⦋0⦌) d = b) :
    (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm b) ⟶ E :=
  (exists_cosliceUniversalPrism_lift p b d hd).choose

/-- 選んだ区間族は指定始点に厳密に始まる。 -/
lemma cosliceUniversalPrismLift_zero {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (b : B _⦋0⦌) (d : E _⦋0⦌)
    (hd : p.app (Opposite.op ⦋0⦌) d = b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ cosliceUniversalPrismLift p b d hd = SSet.const d :=
  (exists_cosliceUniversalPrism_lift p b d hd).choose_spec.1

/-- 恒等錐上の区間全体は、全空間でも同じ指定始点に厳密に定値。 -/
lemma cosliceUniversalPrismLift_identity {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (b : B _⦋0⦌) (d : E _⦋0⦌)
    (hd : p.app (Opposite.op ⦋0⦌) d = b) :
    (Δ[1] ◁ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone b)) ≫
      cosliceUniversalPrismLift p b d hd = SSet.const d :=
  (exists_cosliceUniversalPrism_lift p b d hd).choose_spec.2.1

/-- 持ち上げの底は、元の普遍 coslice 区間族そのもの。 -/
lemma cosliceUniversalPrismLift_projection {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (b : B _⦋0⦌) (d : E _⦋0⦌)
    (hd : p.app (Opposite.op ⦋0⦌) d = b) :
    cosliceUniversalPrismLift p b d hd ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceUniversalPrism b :=
  (exists_cosliceUniversalPrism_lift p b d hd).choose_spec.2.2

/-- 同じ持ち上げの終点を評価した、一つの大域的な coslice 上の射。 -/
def cosliceUniversalPrismLiftEndpoint {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (b : B _⦋0⦌) (d : E _⦋0⦌)
    (hd : p.app (Opposite.op ⦋0⦌) d = b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm b) ⟶ E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ cosliceUniversalPrismLift p b d hd

/-- 終点で得た射は、元の coslice 射影を厳密に被覆する。 -/
lemma cosliceUniversalPrismLiftEndpoint_projection {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (b : B _⦋0⦌) (d : E _⦋0⦌)
    (hd : p.app (Opposite.op ⦋0⦌) d = b) :
    cosliceUniversalPrismLiftEndpoint p b d hd ≫ p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm b) := by
  rw [cosliceUniversalPrismLiftEndpoint, Category.assoc,
    cosliceUniversalPrismLift_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceUniversalPrism_one]

/-- 終点の恒等錐への制限は、指定した同じ点を厳密に回収する。 -/
lemma cosliceUniversalPrismLiftEndpoint_identityMap {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (b : B _⦋0⦌) (d : E _⦋0⦌)
    (hd : p.app (Opposite.op ⦋0⦌) d = b) :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone b) ≫
      cosliceUniversalPrismLiftEndpoint p b d hd = SSet.const d := by
  rw [cosliceUniversalPrismLiftEndpoint, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality,
    Category.assoc, cosliceUniversalPrismLift_identity, SSet.comp_const]

/-- 終点の実際の恒等頂点での値も、指定した元の点そのもの。 -/
lemma cosliceUniversalPrismLiftEndpoint_identity {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (b : B _⦋0⦌) (d : E _⦋0⦌)
    (hd : p.app (Opposite.op ⦋0⦌) d = b) :
    (cosliceUniversalPrismLiftEndpoint p b d hd).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone b) = d := by
  have h := congrArg SSet.yonedaEquiv
    (cosliceUniversalPrismLiftEndpoint_identityMap p b d hd)
  simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, SSet.yonedaEquiv_const] using h

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
