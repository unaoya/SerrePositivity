module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.SliceRoofCorner
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.KanFibrationTools

/-!
# 左ファイブレーションの指定点 slice の相対始点評価

概要：指定点への全錐から、元の始点と底の錐を保持する corner への射は Kan fibration。
方針：全ホーンと点の空境界の pushout join を、最後以外のホーンへ移す。
規約：元の指定点・元の底の全錐を保ち、モデル構造や Kan 全空間を仮定しない。
使われ方：実屋根 slice を次数図式上の始点評価の fiber として比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.SSet _root_.HomotopicalAlgebra _root_.SerrePositivity.InfinityCategories
open _root_.SSet.modelCategoryQuillen
open scoped _root_.Simplicial

lemma joinHorn_point_leftAnodyne (n : ℕ) (i : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinUnion (horn (n + 1) i) (⊥ : (Δ[0] : SSet.{u}).Subcomplex)).ι := by
  let H := horn.{u} ((n + 1) + 0 + 1)
    (Fin.cast (by omega) (i.castAdd (0 + 1)))
  have hh : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions H.ι := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_horn
    change i.val < (n + 1) + 0 + 1
    have := i.isLt
    omega
  rw [← boundary_zero, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.horn_boundary_preimage]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.arrow_mk_iso_iff
    (Arrow.isoMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.subcomplexPreimageIso H (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) 0))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) 0) (by rfl))).2 hh

variable {E B : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ E) (r : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration r]

lemma relativePointSlice_fibration :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeSliceOverMap p (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι r) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.fibration_of_hasLiftingProperty_horn
  intro n i
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeSliceOverMap_hasLiftingProperty _ (horn (n + 1) i) r
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.joinHorn_point_leftAnodyne n i r (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := r))) p

lemma pointSliceCornerMap_fibration : Fibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCornerMap p r) := by
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.relativePointSlice_fibration p r
  have h : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.relativeSliceOverMap p (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι r ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeSliceEmptyCornerMap p r) := inferInstance
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.relativeSliceOverMap_empty_corner] at h
  exact h

lemma pointSliceRoofTriangleMap_fibration {I : SSet.{u}} (a : I ⟶ E) :
    Fibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofTriangleMap r a p) := by
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.pointSliceCornerMap_fibration p r
  apply (SSet.modelCategoryQuillen.fibration_iff _).2
  exact SSet.modelCategoryQuillen.J.rlp.of_isPullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofCorner_isPullback r a p)
    ((SSet.modelCategoryQuillen.fibration_iff _).1 (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.pointSliceCornerMap_fibration p r))

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
