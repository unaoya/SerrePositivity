module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreCoconeLeg
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CosliceFiberVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RetractionTriangle

/-!
概要：元の coslice の恒等余錐へ入る実際の辺から、元の二頂点の retract を回収する。
方針：元の legCompStruct の全二単体を同じ包含・射影・恒等辺の三角形として読む。
規約：元の辺と射影を保持し、retract の存在を入力に要求しない。
使われ方：compact 対象の恒等点の因子化から、元の生成項への retract を構成する。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 元の恒等余錐そのものを、元の coslice 射影の同じ頂点上の点として保持する。 -/
def cosliceIdentityFiberPoint {X : SSet.{u}} (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) x _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone x, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone_projection x).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero x).symm⟩

/-- 元の coslice の恒等点へ入る辺は、元の同じ二頂点を持つ retract を与える。 -/
lemma cosliceIdentityEdge_retract {X : SSet.{u}} {x y : X _⦋0⦌}
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y _⦋0⦌)
    (k : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x)).Edge w.val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf x y := by
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberVertexToEdge w
  let g := (k.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x))).ofEq
    (w.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone_projection x)
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.legCompStruct (c := w.val) k.toTruncated (𝟙 (Δ[0] : SSet.{u}))
  have h : f.CompStruct g (SSet.Edge.id x) := by
    refine ⟨t.simplex, ?_, t.d₀, ?_⟩
    · rw [t.d₂]
      change SSet.yonedaEquiv (_ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (𝟙 Δ[0]) ≫ w.val.val) = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp]
      rfl
    · rw [t.d₁]
      change SSet.yonedaEquiv (_ ≫ _ ≫ SSet.const x) = _
      rw [SSet.comp_const, SSet.comp_const]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one x
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RetractionTriangle.vertexRetraction ⟨f, g, h⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
