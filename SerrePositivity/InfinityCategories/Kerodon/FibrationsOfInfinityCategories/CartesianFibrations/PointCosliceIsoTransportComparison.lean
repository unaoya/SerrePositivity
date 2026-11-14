module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CoslicePostCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLeftMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.LeftFibrationPrismTransport

/-!
概要：底の指定同型による元の coslice fiber 比較と、同じ辺の輸送との全族比較。
方針：元の輸送証人を同じ coslice の後合成で送り、既存の prism 比較を使う。
規約：底や端点を定義的に同一視しない。使われ方：G8 の二重反転からの復帰。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions MorphismSpaces IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：同じ底の同型による fiber 比較は、同じ coslice 全空間の後合成を誘導する。
方針：既存の後合成表示と固定図式の表示変更の座標を使う。
規約：全次数の厳密な等式。使われ方：元の輸送証人の両端の照合。 -/
lemma pointCosliceFiberMap_ι_of_iso {X Y : SSet.{u}} (d : X ≅ Y) (x c : X _⦋0⦌) :
    pointCosliceFiberMap d.hom x c ≫
      vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm (d.hom.app _ x)))
        (d.hom.app _ c) =
      vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm x)) c ≫
        (pointCoslicePostIso d x).hom := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change ((pointCosliceFiberMap d.hom x c).app (Opposite.op ⦋n⦌) s).val.val =
    ((pointCoslicePostIso d x).hom.app (Opposite.op ⦋n⦌) s.val).val
  rw [pointCoslicePostIso_app_val, pointCosliceFiberMap_eq_postcomp]
  simp only [NatTrans.comp_app_apply, PinchedLeftMap.cosliceFiberDiagramIso_app_val]
  rfl

/-- 概要：同じ底の同型で移した coslice 輸送は、元の fiber 比較と輸送の合成に同型。
方針：選ばれた同じ証人を coslice 後合成で送り、prism の輸送比較を適用する。
規約：全 fiber の同型。使われ方：表現可能値の二重反転の自然性。 -/
def pointCosliceIso_transportIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (d : X ≅ Y) (x : X _⦋0⦌) {a b : X _⦋0⦌} (e : X.Edge a b) :
    FunctorIso
      (edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm x)) e ≫
        pointCosliceFiberMap d.hom x b)
      (pointCosliceFiberMap d.hom x a ≫
        edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm (d.hom.app _ x)))
          (e.map d.hom)) := by
  let hT := edgeTransport_isTransport (sliceUnderProjection (SSet.yonedaEquiv.symm x)) e
  let H := hT.choose
  have h₀ := hT.choose_spec.1
  have h₁ := hT.choose_spec.2.1
  have hp := hT.choose_spec.2.2.1
  apply leftFibrationPrism_transportIso
    (sliceUnderProjection (SSet.yonedaEquiv.symm (d.hom.app _ x))) (e.map d.hom)
    (pointCosliceFiberMap d.hom x a)
    (edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm x)) e ≫
      pointCosliceFiberMap d.hom x b)
    (H ≫ (pointCoslicePostIso d x).hom)
  · rw [← Category.assoc, h₀, ← pointCosliceFiberMap_ι_of_iso]
  · rw [← Category.assoc, h₁, Category.assoc, ← pointCosliceFiberMap_ι_of_iso]
    simp only [Category.assoc]
  · rw [Category.assoc, pointCoslicePostIso_projection, ← Category.assoc, hp]
    rw [SSet.Edge.map_edge, Category.assoc, SSet.yonedaEquiv_symm_comp]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
