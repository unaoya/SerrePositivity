module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexPrismFirstVertex

/-!
概要：left fibration の持ち上げを、固定した部分図式と部分パラメーターを同時に保って延長する。
方針：left anodyne な包含とパラメーターの単射の pushout-product に対する持ち上げを使う。
規約：底の族はパラメーターに依存してよい。モデル構造は使わない。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、相対表現と高次の持ち上げのパラメーター付き延長。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：left anodyne な部分図式を固定した持ち上げは、指定済みの部分パラメーターも保って延長できる。
方針：二つの指定図式を pushout に貼り、その left anodyne な包含を持ち上げる。
規約：底 b のパラメーター依存を制限しない。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、境界上で指定済みの整合性を保つ相対延長。 -/
lemma leftFibration_lift_relative_parameters {D A K L X Y : SSet.{u}}
    (p : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (i : D ⟶ A) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i)
    (j : K ⟶ L) [Mono j]
    (u : A ⊗ K ⟶ X) (v : D ⊗ L ⟶ X) (b : A ⊗ L ⟶ Y)
    (hw : (i ▷ K) ≫ u = (D ◁ j) ≫ v)
    (hu : u ≫ p = (A ◁ j) ≫ b) (hv : v ≫ p = (i ▷ L) ≫ b) :
    ∃ W : A ⊗ L ⟶ X,
      (A ◁ j) ≫ W = u ∧ (i ▷ L) ≫ W = v ∧ W ≫ p = b := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i j
  let w := sq.isPushout.desc u v hw
  have hwp : w ≫ p = sq.ι ≫ b := by
    apply sq.hom_ext
    · simp only [w, ← Category.assoc, sq.isPushout.inl_desc, sq.inl_ι]
      exact hu
    · simp only [w, ← Category.assoc, sq.isPushout.inr_desc, sq.inr_ι]
      exact hv
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_pushoutObjObj_left i hi j sq p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))
  let c : CommSq w sq.ι p b := ⟨hwp⟩
  have hl : sq.inl ≫ sq.ι = A ◁ j := sq.inl_ι
  have hr : sq.inr ≫ sq.ι = i ▷ L := sq.inr_ι
  refine ⟨c.lift, ?_, ?_, c.fac_right⟩
  · rw [← hl, Category.assoc, c.fac_left]
    exact sq.isPushout.inl_desc _ _ _
  · rw [← hr, Category.assoc, c.fac_left]
    exact sq.isPushout.inr_desc _ _ _

/-- 概要：単体の prism の最初の値を固定した持ち上げは、部分パラメーターを保って全体へ延長できる。
方針：最初の頂点とパラメーター A の積の left anodyne 性を一般の相対延長へ使う。
規約：n は任意。底の族 b は拡張するパラメーター L に依存してよい。
使われ方：Kerodon Corollary 5.6.5.15（Tag 0296）、coherent な変換の高次の比較の相対的な構成。 -/
lemma leftFibration_extend_simplexLift_parameters {A K L X Y : SSet.{u}}
    (p : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (n : ℕ) (j : K ⟶ L) [Mono j]
    (u : ((Δ[n] : SSet.{u}) ⊗ A) ⊗ K ⟶ X)
    (v : ((Δ[0] : SSet.{u}) ⊗ A) ⊗ L ⟶ X)
    (b : ((Δ[n] : SSet.{u}) ⊗ A) ⊗ L ⟶ Y)
    (hw : ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n ▷ A) ▷ K) ≫ u = ((Δ[0] ⊗ A) ◁ j) ≫ v)
    (hu : u ≫ p = ((Δ[n] ⊗ A) ◁ j) ≫ b)
    (hv : v ≫ p = ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n ▷ A) ▷ L) ≫ b) :
    ∃ W : ((Δ[n] : SSet.{u}) ⊗ A) ⊗ L ⟶ X,
      ((Δ[n] ⊗ A) ◁ j) ≫ W = u ∧
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n ▷ A) ▷ L) ≫ W = v ∧ W ≫ p = b :=
  leftFibration_lift_relative_parameters p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n ▷ A)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismFirstVertex_leftAnodyne n A) j u v b hw hu hv

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
