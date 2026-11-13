module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenASliceOpposite
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.VertexFiberTotalIso
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.OppositeVertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrismOpposite

/-!
概要：頂点上の右 slice の prism を反対の単体集合の左 coslice へ移す。
方針：既存の底上の slice 反転同型を prism と fiber に同時に作用させる。
規約：反転によって時間の両端とパラメーターの向きが変わる。
使われ方：coherent な合成 prism から左 coslice の輸送族を構成する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：右 slice の fiber の反転を反対の頂点からの左 coslice fiber へ移す同型。
方針：fiber の反転同型と底上の正規化済み slice 同型を合成する。
規約：元の始点 x は反転後の終点となる。
使われ方：合成 prism の両端を fiber 値の射として保持する。 -/
def pointSliceReverseFiberIso {B : SSet.{u}} (z x : B _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm z)) x).op ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm z)))
        (SSet.opObjEquiv.symm x) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.oppositeVertexFiberIso _ x ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberTotalIso _ _
    ((Over.forget B.op).mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointSliceOverOpIso z))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointSliceOverOpIso z).hom.w (SSet.opObjEquiv.symm x)

/-- 概要：fiber の反転同型は全空間への包含を保つ。
方針：二つの同型の包含の式を順に使う。
規約：全空間側は正規化済みの slice 反転同型。
使われ方：反転した prism の両端の確認。 -/
lemma pointSliceReverseFiberIso_ι {B : SSet.{u}} (z x : B _⦋0⦌) :
    (pointSliceReverseFiberIso z x).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm z)))
        (SSet.opObjEquiv.symm x) =
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm z)) x) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointSliceOverOpIso z).hom.left := by
  rfl

/-- 概要：右 slice の prism を左 coslice に反転する。
方針：prism の反転の後で正規化済みの slice 反転同型を適用する。
規約：区間は第一因子、パラメーターは反転する。
使われ方：標準合成の高次データの双対化。 -/
def reversePointSlicePrism {A B : SSet.{u}} (z : B _⦋0⦌)
    (H : Δ[1] ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z)) :
    Δ[1] ⊗ A.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm z)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism H ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointSliceOverOpIso z).hom.left

/-- 概要：slice の prism の反転は射影と可換。
方針：底上の同型の可換性と prism の後合成の自然性を使う。
規約：底も反転し、端点の方向も反転する。
使われ方：標準輸送族の底の式。 -/
lemma reversePointSlicePrism_projection {A B : SSet.{u}} (z : B _⦋0⦌)
    (H : Δ[1] ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z)) :
    reversePointSlicePrism z H ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm z)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism (H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm z)) := by
  dsimp only [reversePointSlicePrism]
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointSliceOverOpIso z).hom.w
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointSliceOverOpIso z).hom.left ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm z)) =
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm z)) at h
  rw [Category.assoc, h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_postcomp]

/-- 概要：右 slice の prism の反転は fiber 値の両端を反転して保つ。
方針：端点の反転公式に fiber の包含の可換性を適用する。
規約：元の端点 i.rev が反転後の端点 i になる。
使われ方：輸送族の始点と終点を高次パラメーターごと保持する。 -/
lemma reversePointSlicePrism_endpoint {A B : SSet.{u}} (z x : B _⦋0⦌)
    (H : Δ[1] ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z)) (i : Fin 2)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm z)) x)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i.rev A ≫ H = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i A.op ≫ reversePointSlicePrism z H =
      SSet.opFunctor.map f ≫ (pointSliceReverseFiberIso z x).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ := by
  dsimp only [reversePointSlicePrism]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_endpoint, hf, SSet.opFunctor.map_comp,
    Category.assoc, pointSliceReverseFiberIso_ι]

/-- 概要：slice prism の反転はパラメーターの制限と可換。
方針：prism の反転の自然性を同型の前で使う。
規約：制限の射も反転する。
使われ方：全パラメーター付き輸送の係数・底の制限。 -/
lemma reversePointSlicePrism_precomp {A D B : SSet.{u}} (z : B _⦋0⦌)
    (f : D ⟶ A) (H : Δ[1] ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z)) :
    reversePointSlicePrism z ((Δ[1] ◁ f) ≫ H) =
      (Δ[1] ◁ SSet.opFunctor.map f) ≫ reversePointSlicePrism z H := by
  dsimp only [reversePointSlicePrism]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_precomp, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
