module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.PinchedSliceCompositionRealization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.LeftFibrationPrismTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.OppositeVertexFiber

/-!
概要：元の pinched Hom の実 slice 円柱を、反対 left fibration の同じ輸送へ比較する。
方針：元の全円柱を反転し、同じ fiber の順序同型を介して標準輸送の一意性を使う。
規約：D の汎用補題は許可された新規の葉からだけ読み取り専用 import する。
使われ方：表現可能前層の分類辺の反転から元の Hom 前合成の同値性へ戻す。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

variable {X : SSet.{u}} [Quasicategory X] (z : X _⦋0⦌)
local notation "p" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm z)

/-- 概要：同じ pinched Hom の反転を反対 slice の同じ fiber と同定する。
方針：二つの既存の厳密な fiber 同型を合成。
規約：同じ終点と始点。使われ方：輸送比較の両端。 -/
def pinchedOppositeSliceFiberIso (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x z).op ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (SSet.opFunctor.map p) (SSet.opObjEquiv.symm x) :=
  SSet.opFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso x z) ≪≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.oppositeVertexFiberIso p x

/-- 概要：元の実 slice 円柱は、反対側の同じ指定辺に沿う標準輸送を表す。
方針：全 prism を反転して標準輸送と比較。
規約：元の係数射。使われ方：分類辺が反転する場合の前合成の反映。 -/
def pinchedSlicePrism_oppositeTransportIso {x y : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) x y)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y z ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x z)
    (H : (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y z ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm z))
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H = c ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilySlice X x z)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilySlice X y z)
    (hp : H ≫ p = fst (Δ[1] : SSet.{u}) _ ≫ SSet.yonedaEquiv.symm e.edge) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.opFunctor.map c ≫ (pinchedOppositeSliceFiberIso z x).hom)
      ((pinchedOppositeSliceFiberIso z y).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport (SSet.opFunctor.map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.leftFibrationPrism_transportIso (SSet.opFunctor.map p)
    (SSet.Edge.ofTruncated (X := X.op) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e))
    (pinchedOppositeSliceFiberIso z y).hom
    (SSet.opFunctor.map c ≫ (pinchedOppositeSliceFiberIso z x).hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism H)
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_endpoint]
    change SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H) = _
    rw [h₁]
    simp only [pinchedOppositeSliceFiberIso, Iso.trans_hom, Functor.mapIso_hom,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.oppositeVertexFiberIso_hom_ι, ← Functor.map_comp]
    rfl
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_endpoint]
    change SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ H) = _
    rw [h₀]
    simp only [pinchedOppositeSliceFiberIso, Iso.trans_hom, Functor.mapIso_hom,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.oppositeVertexFiberIso_hom_ι, ← Functor.map_comp]
    rfl
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.reversePrism_postcomp, hp]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
