module

public import SerrePositivity.KST.LocalizingInvariants.VerdierSimplexTerminalRefinement
public import SerrePositivity.KST.LocalizingInvariants.SimplexTerminalCoconeExtension

/-!
概要：終端分母による全図式の精密化に、次の指定辺を厳密に貼る。
方針：同じ列四角形を保持した pullback 精密化から終端の等号を回収し、余錐を延長する。
規約：全次数（零次を含む）、元の全図式への分母、次の全辺を保持する。
使われ方：Verdier 商の有限線型図式を帰納的に持ち上げる際の始域側の工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

private def edgeWithEndpoints {X : SSet.{u}} {a b c d : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) a b) (ha : a = c) (hb : b = d) :
    Truncated.Edge (X := (truncation 2).obj X) c d := ha ▸ hb ▸ e

private lemma edgeWithEndpoints_edge {X : SSet.{u}} {a b c d : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) a b) (ha : a = c) (hb : b = d) :
    (edgeWithEndpoints e ha hb).edge = e.edge := by
  subst c
  subst d
  rfl

/-- 元の strict core 逆像の分母を、商後の全関手圏における同じ辺の同型へ戻す。 -/
def simplexDenominatorImageIso {B C : StableCategory.{u}} (q : ExactMap B C)
    {n : ℕ} {D E : (Δ[n] : SSet.{u}) ⟶ B.obj}
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
      (functorVertex D) (functorVertex E))
    (ht : t.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌)) :
    FunctorIso (D ≫ q.hom) (E ≫ q.hom) := by
  let e := t.map ((truncation 2).map ((ihom (Δ[n] : SSet.{u})).map q.hom))
  have hi : IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj C.obj) e := by
    have hc := (quasicategoryCore_mem_edge_iff _).mp ht
    exact (isInvertibleEdge_congr (e := edgeOfSimplex
      (((ihom (Δ[n] : SSet.{u})).map q.hom).app (Opposite.op ⦋1⦌) t.edge))
      (f := e) rfl).mp hc
  exact asIso (Truncated.HomotopyCategory.homMk e)

/-- 比較同型の順方向は、元の同じ分母を商後合成した実辺の類。 -/
lemma simplexDenominatorImageIso_hom {B C : StableCategory.{u}} (q : ExactMap B C)
    {n : ℕ} {D E : (Δ[n] : SSet.{u}) ⟶ B.obj}
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
      (functorVertex D) (functorVertex E))
    (ht : t.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌)) :
    (simplexDenominatorImageIso q t ht).hom = Truncated.HomotopyCategory.homMk
      (t.map ((truncation 2).map ((ihom (Δ[n] : SSet.{u})).map q.hom))) := rfl

/-- 元の全図式への分母と、指定した次の全辺を保つ実余錐を同時に構成する。 -/
lemma exists_verdierSimplexRefinementCocone {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    {y z : B.obj _⦋0⦌}
    (s : Truncated.Edge (X := (truncation 2).obj B.obj) y
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (g : Truncated.Edge (X := (truncation 2).obj B.obj) y z)
    (hs : s.edge ∈ weakEquivalences i) :
    ∃ (D' : (Δ[n] : SSet.{u}) ⟶ B.obj)
      (t : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
        (functorVertex D') (functorVertex D)) (c : JoinCocone D'),
      t.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) ∧
      D'.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)) = y ∧
      c.vertex = z ∧
      (joinStdSimplexIso 0 0).inv ≫
        joinMap (simplexLastPoint n) (𝟙 (Δ[0] : SSet.{u})) ≫ c.val =
          SSet.yonedaEquiv.symm g.edge := by
  let sm := SSet.yonedaEquiv.symm s.edge
  have hsm : sm.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)) := by
    have hv : SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
      apply SSet.yonedaEquiv.injective
      decide
    have he := congrArg SSet.yonedaEquiv (edgeSimplex_target s)
    rw [← hv, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply] at he
    exact he
  have hs' : SSet.yonedaEquiv sm ∈ weakEquivalences i := by
    change SSet.yonedaEquiv (SSet.yonedaEquiv.symm s.edge) ∈ weakEquivalences i
    rw [Equiv.apply_symm_apply]
    exact hs
  obtain ⟨Q, _, horig, hlast, hW⟩ :=
    exists_verdierSimplexTerminalRefinement h D sm hsm hs'
  let D' := (functorVertexEquiv (Δ[n] : SSet.{u}) B.obj).symm (squareVertex Q 0 0)
  have hD' : functorVertex D' = squareVertex Q 0 0 := Equiv.apply_symm_apply _ _
  have hv : D'.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)) = y := by
    have he := congrArg (fun R => squareVertex R 0 0) hlast
    have hd := congrArg ((evaluateFunctorAt (Y := B.obj)
      (stdSimplex.obj₀Equiv.symm (Fin.last n))).app (Opposite.op ⦋0⦌)) hD'
    rw [evaluateFunctorAt_functorVertex] at hd
    exact hd.trans (he.trans (by
      change sm.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = y
      have hp : SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
          (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
        apply SSet.yonedaEquiv.injective
        decide
      have hsrc := congrArg SSet.yonedaEquiv (edgeSimplex_source s)
      rw [← hp, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply] at hsrc
      exact hsrc))
  have hpoint : SSet.yonedaEquiv (simplexLastPoint n ≫ D') = y := by
    rw [SSet.yonedaEquiv_comp, simplexLastPoint, Equiv.apply_symm_apply]
    exact hv
  let g' : Truncated.Edge (X := (truncation 2).obj B.obj)
      (SSet.yonedaEquiv (simplexLastPoint n ≫ D')) z :=
    edgeWithEndpoints g hpoint.symm rfl
  obtain ⟨c, hc, hedge⟩ := exists_simplexCocone_of_last_edge D' g'
  have ht : squareVertex Q 0 0 = functorVertex D' := hD'.symm
  let t : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
      (functorVertex D') (functorVertex D) := edgeWithEndpoints (squareLeftArrow Q) ht horig
  refine ⟨D', t, c, ?_, hv, hc, ?_⟩
  · simpa only [t, edgeWithEndpoints_edge] using hW
  · simpa only [g', edgeWithEndpoints_edge] using hedge

end SerrePositivity.KST.LocalizingInvariants
