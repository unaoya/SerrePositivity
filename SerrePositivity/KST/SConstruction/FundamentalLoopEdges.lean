module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyGroups
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyCategoryBridge

/-! # 境界定数一次単体とホモトピー圏の loop 辺
概要：既存の基本群の代表と、端点つき loop 辺の代表を厳密に比較する。
方針：Yoneda と二端点の境界条件で同値を作り、乗法の二単体を合成構造へ移す。
規約：辺の向きを保持する。使われ方：基本亜群の表示を既存の Kan 基本群へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 境界定数な一次単体を、同じ頂点から同じ頂点への端点つき辺へ移す。 -/
def fundamentalLoopEdge {B : SSet.{u}} {x : B _⦋0⦌} (s : B.PtSimplex 1 x) :
    SSet.Truncated.Edge (X := (truncation 2).obj B) x x where
  edge := SSet.yonedaEquiv s.map
  src_eq := by
    change B.δ 1 (SSet.yonedaEquiv s.map) = x
    rw [← stdSimplex.yonedaEquiv_δ_comp, s.δ_map, SSet.yonedaEquiv_const]
  tgt_eq := by
    change B.δ 0 (SSet.yonedaEquiv s.map) = x
    rw [← stdSimplex.yonedaEquiv_δ_comp, s.δ_map, SSet.yonedaEquiv_const]

/-- 端点つき loop 辺を、同じ境界定数な一次単体へ戻す。 -/
def fundamentalLoopSimplex {B : SSet.{u}} {x : B _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj B) x x) : B.PtSimplex 1 x where
  map := SSet.yonedaEquiv.symm e.edge
  comm := by
    apply boundary.hom_ext
    intro i
    simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, SSet.comp_const]
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, SSet.yonedaEquiv_const]
    fin_cases i
    · exact e.tgt_eq
    · exact e.src_eq

/-- 元の境界定数一次単体と端点つき loop 辺は同じ代表を持つ。 -/
def fundamentalLoopEdgeEquiv (B : SSet.{u}) (x : B _⦋0⦌) :
    B.PtSimplex 1 x ≃ SSet.Truncated.Edge (X := (truncation 2).obj B) x x where
  toFun := fundamentalLoopEdge
  invFun := fundamentalLoopSimplex
  left_inv s := by
    apply RelativeMorphism.ext
    exact SSet.yonedaEquiv.symm_apply_apply s.map
  right_inv e := by
    apply SSet.Truncated.Edge.ext
    exact SSet.yonedaEquiv.apply_symm_apply e.edge

/-- 定数単体は元の頂点の恒等辺を与える。 -/
lemma fundamentalLoopEdge_const {B : SSet.{u}} (x : B _⦋0⦌) :
    fundamentalLoopEdge (.const : B.PtSimplex 1 x) =
      SSet.Truncated.Edge.id (X := (truncation 2).obj B) x := by
  apply SSet.Truncated.Edge.ext
  change SSet.yonedaEquiv (SSet.const x : (Δ[1] : SSet.{u}) ⟶ B) = B.σ 0 x
  have h := stdSimplex.σ_comp_yonedaEquiv_symm x (0 : Fin 1)
  rw [SSet.yonedaEquiv_symm_zero, SSet.comp_const] at h
  exact (congrArg SSet.yonedaEquiv h).trans (SSet.yonedaEquiv.apply_symm_apply _)

/-- 基本群の乗法を表す元の二単体はホモトピー圏の辺の合成構造を与える。 -/
def fundamentalLoopMulToComp {B : SSet.{u}} {x : B _⦋0⦌}
    {f g h : B.PtSimplex 1 x} (r : PtSimplex.MulStruct f g h (0 : Fin 1)) :
    SSet.Truncated.Edge.CompStruct (fundamentalLoopEdge f) (fundamentalLoopEdge g)
      (fundamentalLoopEdge h) where
  simplex := SSet.yonedaEquiv r.map
  d₂ := by
    change B.δ 2 (SSet.yonedaEquiv r.map) = SSet.yonedaEquiv f.map
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    exact congrArg SSet.yonedaEquiv r.δ_succ_succ_map
  d₀ := by
    change B.δ 0 (SSet.yonedaEquiv r.map) = SSet.yonedaEquiv g.map
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    exact congrArg SSet.yonedaEquiv r.δ_castSucc_castSucc_map
  d₁ := by
    change B.δ 1 (SSet.yonedaEquiv r.map) = SSet.yonedaEquiv h.map
    rw [← stdSimplex.yonedaEquiv_δ_comp]
    exact congrArg SSet.yonedaEquiv r.δ_succ_castSucc_map

/-- 同じ loop 辺の合成構造を、元の基本群の乗法の二単体へ戻す。 -/
def fundamentalLoopCompToMul {B : SSet.{u}} {x : B _⦋0⦌}
    {f g h : B.PtSimplex 1 x}
    (r : SSet.Truncated.Edge.CompStruct (fundamentalLoopEdge f) (fundamentalLoopEdge g)
      (fundamentalLoopEdge h)) : PtSimplex.MulStruct f g h (0 : Fin 1) where
  map := SSet.yonedaEquiv.symm r.simplex
  δ_castSucc_castSucc_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact (congrArg SSet.yonedaEquiv.symm r.d₀).trans (SSet.yonedaEquiv.symm_apply_apply _)
  δ_succ_castSucc_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact (congrArg SSet.yonedaEquiv.symm r.d₁).trans (SSet.yonedaEquiv.symm_apply_apply _)
  δ_succ_succ_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    exact (congrArg SSet.yonedaEquiv.symm r.d₂).trans (SSet.yonedaEquiv.symm_apply_apply _)
  δ_map_of_lt j hj := by simp at hj
  δ_map_of_gt j hj := by
    have h : (2 : Fin 3) < j := hj
    omega

end SerrePositivity.KST.SConstruction
