module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyGroups
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat

/-!
概要：元の境界定数一単体と基点 loop の辺、積の充填と合成三角形を厳密に対応させる。
方針：Yoneda と二つの端点の式を使い、元の三面をそのまま移す。
規約：積は左から右の経路合成。使われ方：基本群の類と Hom のホモトピー圏の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.FundamentalLoop
variable {X : SSet.{u}} {x : X _⦋0⦌}

/-- 元の境界定数一単体を、同じ基点での loop の辺に読む。 -/
def edge (s : X.PtSimplex 1 x) : X.Edge x x :=
  SSet.Edge.mk (SSet.yonedaEquiv s.map)
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, PtSimplex.δ_map, SSet.yonedaEquiv_const])
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, PtSimplex.δ_map, SSet.yonedaEquiv_const])

/-- 元の loop の辺を、同じ一単体の境界定数写像へ戻す。 -/
def simplex (e : X.Edge x x) : X.PtSimplex 1 x where
  map := SSet.yonedaEquiv.symm e.edge
  comm := by
    ext j : 1
    simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, SSet.comp_const]
    fin_cases j
    · rw [stdSimplex.δ_comp_yonedaEquiv_symm]
      exact (congrArg SSet.yonedaEquiv.symm e.tgt_eq).trans (SSet.yonedaEquiv_symm_zero x)
    · rw [stdSimplex.δ_comp_yonedaEquiv_symm]
      exact (congrArg SSet.yonedaEquiv.symm e.src_eq).trans (SSet.yonedaEquiv_symm_zero x)

/-- loop の辺を往復しても元の辺そのもの。 -/
lemma edge_simplex (e : X.Edge x x) : edge (simplex e) = e :=
  SSet.Edge.ext (Equiv.apply_symm_apply _ _)

/-- 境界定数単体を往復しても元の単体そのもの。 -/
lemma simplex_edge (s : X.PtSimplex 1 x) : simplex (edge s) = s :=
  RelativeMorphism.ext (Equiv.symm_apply_apply _ _)

/-- 定値単体は、同じ元の基点の恒等辺を与える。 -/
lemma edge_const : edge (.const : X.PtSimplex 1 x) = SSet.Edge.id x := by
  apply SSet.Edge.ext
  change SSet.yonedaEquiv (SSet.const x : (Δ[1] : SSet.{u}) ⟶ X) = X.σ 0 x
  have h := stdSimplex.yonedaEquiv_σ_comp (SSet.const x : (Δ[0] : SSet.{u}) ⟶ X) (0 : Fin 1)
  rw [SSet.comp_const, SSet.yonedaEquiv_const] at h
  exact h

/-- 元の積の充填は、同じ三つの loop 辺の合成構造を与える。 -/
def compStruct {s t r : X.PtSimplex 1 x}
    (h : PtSimplex.MulStruct s t r (0 : Fin 1)) :
    SSet.Edge.CompStruct (edge s) (edge t) (edge r) :=
  SSet.Edge.CompStruct.mk (SSet.yonedaEquiv h.map)
    (by rw [← stdSimplex.yonedaEquiv_δ_comp]
        exact congrArg SSet.yonedaEquiv h.δ_succ_succ_map)
    (by rw [← stdSimplex.yonedaEquiv_δ_comp]
        exact congrArg SSet.yonedaEquiv h.δ_castSucc_castSucc_map)
    (by rw [← stdSimplex.yonedaEquiv_δ_comp]
        exact congrArg SSet.yonedaEquiv h.δ_succ_castSucc_map)

/-- 同じ loop 辺の元の合成三角形は、境界定数一単体の積の充填へ戻る。 -/
def mulStruct {s t r : X.PtSimplex 1 x}
    (h : SSet.Edge.CompStruct (edge s) (edge t) (edge r)) :
    PtSimplex.MulStruct s t r (0 : Fin 1) where
  map := SSet.yonedaEquiv.symm h.simplex
  δ_castSucc_castSucc_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    change SSet.yonedaEquiv.symm (X.δ 0 h.simplex) = _
    rw [h.d₀]
    exact Equiv.symm_apply_apply _ _
  δ_succ_castSucc_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    change SSet.yonedaEquiv.symm (X.δ 1 h.simplex) = _
    rw [h.d₁]
    exact Equiv.symm_apply_apply _ _
  δ_succ_succ_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm]
    change SSet.yonedaEquiv.symm (X.δ 2 h.simplex) = _
    rw [h.d₂]
    exact Equiv.symm_apply_apply _ _
  δ_map_of_lt j hj := by simp at hj
  δ_map_of_gt j hj := by fin_cases j <;> simp at hj

end SerrePositivity.KST.Spectra.FundamentalLoop
