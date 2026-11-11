module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreCoconeLeg
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness

/-!
概要：図式の辺と余錐の二つの脚が成す、実際の合成三角形を構成する。
方針：辺と余錐頂点の join を標準二単体へ移し、全ての面を計算する。
規約：図式と余錐は任意。脚の始点は元の図式の指定頂点の像に正規化する。
使われ方：部分余極限対象の span の余錐から、二枝の比較射の合成の一致を取り出す。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)

/-- 元の図式の頂点で始まるように端点を正規化した、余錐の実際の脚。 -/
def coconeVertexLeg (a : K _⦋0⦌) : X.Edge (p.app (Opposite.op ⦋0⦌) a) c.vertex := by
  let e := c.leg (SSet.yonedaEquiv.symm a)
  refine SSet.Edge.ofTruncated ⟨e.edge, e.src_eq.trans ?_, e.tgt_eq⟩
  rw [SSet.yonedaEquiv_comp]
  exact congrArg (fun v ↦ p.app (Opposite.op ⦋0⦌) v) (Equiv.apply_symm_apply _ a)

/-- 辺と点の join の面を、端点の join へ制限する式。 -/
lemma joinEdgePoint_face_inv (i : Fin 2) :
    stdSimplex.δ i.castSucc ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 1 0).inv =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ i) (𝟙 Δ[0]) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_vertex, Iso.inv_hom_id_assoc]

/-- 図式の辺に沿う二つの脚の可換性は、指定した実際の合成二単体で証明できる。 -/
def coconeVertexLegCompStruct {a b : K _⦋0⦌} (e : K.Edge a b) :
    SSet.Truncated.Edge.CompStruct (e.map p).toTruncated (coconeVertexLeg c b).toTruncated
      (coconeVertexLeg c a).toTruncated := by
  let T := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm e.edge) (𝟙 Δ[0]) ≫ c.val
  have h₂ : stdSimplex.δ (2 : Fin 3) ≫ T = SSet.yonedaEquiv.symm e.edge ≫ p := by
    have h : stdSimplex.δ (2 : Fin 3) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} 1 0).inv =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[1] Δ[0] := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_inl, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    dsimp only [T]
    rw [← Category.assoc, h, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, c.property]
  have hface (i : Fin 2) : stdSimplex.δ i.castSucc ≫ T =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ i ≫ SSet.yonedaEquiv.symm e.edge) (𝟙 Δ[0]) ≫ c.val := by
    dsimp only [T]
    rw [← Category.assoc, joinEdgePoint_face_inv, Category.assoc,
      ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ i) (𝟙 Δ[0])), ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
  refine { simplex := SSet.yonedaEquiv T, d₂ := ?_, d₀ := ?_, d₁ := ?_ }
  · change X.δ 2 (SSet.yonedaEquiv T) = p.app (Opposite.op ⦋1⦌) e.edge
    rw [← stdSimplex.yonedaEquiv_δ_comp, h₂, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  · change X.δ 0 (SSet.yonedaEquiv T) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    erw [hface (0 : Fin 2), e.δ_zero_yonedaEquiv_symm]
    rfl
  · change X.δ 1 (SSet.yonedaEquiv T) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    erw [hface (1 : Fin 2), e.δ_one_yonedaEquiv_symm]
    rfl

/-- 任意の余錐の二つの脚は、元の図式の辺とホモトピー圏で可換な三角形を成す。 -/
lemma coconeVertexLeg_comp {a b : K _⦋0⦌} (e : K.Edge a b) :
    SSet.Truncated.HomotopyCategory.homMk (e.map p).toTruncated ≫
        SSet.Truncated.HomotopyCategory.homMk (coconeVertexLeg c b).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (coconeVertexLeg c a).toTruncated :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk (coconeVertexLegCompStruct c e)

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
