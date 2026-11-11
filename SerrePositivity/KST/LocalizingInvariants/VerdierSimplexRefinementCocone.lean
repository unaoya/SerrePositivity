module

public import SerrePositivity.KST.LocalizingInvariants.VerdierSimplexTerminalRefinement
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.SimplexTerminalCoconeExtension

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
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
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
def simplexDenominatorImageIso {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : ℕ} {D E : (Δ[n] : SSet.{u}) ⟶ B.obj}
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex E))
    (ht : t.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (D ≫ q.hom) (E ≫ q.hom) := by
  let e := t.map ((truncation 2).map ((ihom (Δ[n] : SSet.{u})).map q.hom))
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj C.obj) e := by
    have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_mem_edge_iff _).mp ht
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      (((ihom (Δ[n] : SSet.{u})).map q.hom).app (Opposite.op ⦋1⦌) t.edge))
      (f := e) rfl).mp hc
  exact asIso (Truncated.HomotopyCategory.homMk e)

/-- 比較同型の順方向は、元の同じ分母を商後合成した実辺の類。 -/
lemma simplexDenominatorImageIso_hom {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : ℕ} {D E : (Δ[n] : SSet.{u}) ⟶ B.obj}
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex E))
    (ht : t.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌)) :
    (simplexDenominatorImageIso q t ht).hom = Truncated.HomotopyCategory.homMk
      (t.map ((truncation 2).map ((ihom (Δ[n] : SSet.{u})).map q.hom))) := rfl

/-- 比較の指定成分は、同じ元の分母成分の商像として厳密に回収される。 -/
lemma simplexDenominatorImageIso_evaluation_hom {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : ℕ} {D E : (Δ[n] : SSet.{u}) ⟶ B.obj}
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex E))
    (ht : t.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌))
    (k : (Δ[n] : SSet.{u}) _⦋0⦌) {x y : B.obj _⦋0⦌}
    (s : Truncated.Edge (X := (truncation 2).obj B.obj) x y)
    (heval : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B.obj) k).app (Opposite.op ⦋1⦌) t.edge = s.edge) :
    Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C.obj) k)).toFunctor.map
      (simplexDenominatorImageIso q t ht).hom) =
        Arrow.mk (Truncated.HomotopyCategory.homMk (s.map ((truncation 2).map q.hom))) := by
  have hn : (ihom (Δ[n] : SSet.{u})).map q.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C.obj) k =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B.obj) k ≫ q.hom := rfl
  have hc := ConcreteCategory.congr_hom (C := Type u)
    (NatTrans.congr_app hn (Opposite.op ⦋1⦌)) t.edge
  have he := hc.trans (congrArg (q.hom.app (Opposite.op ⦋1⦌)) heval)
  exact Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ he

/-- 元の全図式を精密化し、終端で元の指定分母の一次単体そのものを回収する。 -/
lemma exists_verdierSimplexTerminalRefinementMap {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    {y : B.obj _⦋0⦌}
    (s : Truncated.Edge (X := (truncation 2).obj B.obj) y
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (hs : s.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) :
    ∃ (D' : (Δ[n] : SSet.{u}) ⟶ B.obj)
      (t : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D') (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D)),
      t.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) ∧
      D'.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)) = y ∧
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B.obj) (stdSimplex.obj₀Equiv.symm (Fin.last n))).app
        (Opposite.op ⦋1⦌) t.edge = s.edge := by
  let sm := SSet.yonedaEquiv.symm s.edge
  have hsm : sm.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)) := by
    have hv : SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
      apply SSet.yonedaEquiv.injective
      decide
    have he := congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target s)
    rw [← hv, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply] at he
    exact he
  have hs' : SSet.yonedaEquiv sm ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
    change SSet.yonedaEquiv (SSet.yonedaEquiv.symm s.edge) ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i
    rw [Equiv.apply_symm_apply]
    exact hs
  obtain ⟨Q, _, horig, hlast, hW⟩ :=
    exists_verdierSimplexTerminalRefinement h D sm hsm hs'
  let D' := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[n] : SSet.{u}) B.obj).symm (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex Q 0 0)
  have hD' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D' = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex Q 0 0 := Equiv.apply_symm_apply _ _
  have hv : D'.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)) = y := by
    have he := congrArg (fun R => _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex R 0 0) hlast
    have hd := congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B.obj)
      (stdSimplex.obj₀Equiv.symm (Fin.last n))).app (Opposite.op ⦋0⦌)) hD'
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at hd
    exact hd.trans (he.trans (by
      change sm.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = y
      have hp : SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
          (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
        apply SSet.yonedaEquiv.injective
        decide
      have hsrc := congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_source s)
      rw [← hp, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply] at hsrc
      exact hsrc))
  have ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex Q 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D' := hD'.symm
  let t : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D') (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D) := edgeWithEndpoints (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow Q) ht horig
  refine ⟨D', t, ?_, hv, ?_⟩
  · simpa only [t, edgeWithEndpoints_edge] using hW
  · rw [show t.edge = (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow Q).edge from edgeWithEndpoints_edge _ _ _,
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareLeftArrow_edge, ← SSet.yonedaEquiv_comp, Category.assoc, hlast]
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram sm) = s.edge
    simp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge, lift_snd,
      Category.id_comp]
    exact Equiv.apply_symm_apply _ _

/-- 元の全図式への分母と、指定した次の全辺を保つ実余錐を同時に構成する。 -/
lemma exists_verdierSimplexRefinementCocone {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    {y z : B.obj _⦋0⦌}
    (s : Truncated.Edge (X := (truncation 2).obj B.obj) y
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (g : Truncated.Edge (X := (truncation 2).obj B.obj) y z)
    (hs : s.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) :
    ∃ (D' : (Δ[n] : SSet.{u}) ⟶ B.obj)
      (t : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D') (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D)) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D'),
      t.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) ∧
      D'.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)) = y ∧
      c.vertex = z ∧
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 (Δ[0] : SSet.{u})) ≫ c.val =
          SSet.yonedaEquiv.symm g.edge := by
  obtain ⟨D', t, ht, hv, _⟩ := exists_verdierSimplexTerminalRefinementMap h D s hs
  have hpoint : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n ≫ D') = y := by
    rw [SSet.yonedaEquiv_comp, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint, Equiv.apply_symm_apply]
    exact hv
  let g' : Truncated.Edge (X := (truncation 2).obj B.obj)
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n ≫ D')) z :=
    edgeWithEndpoints g hpoint.symm rfl
  obtain ⟨c, hc, hedge⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.exists_simplexCocone_of_last_edge D' g'
  refine ⟨D', t, c, ht, hv, hc, ?_⟩
  · simpa only [g', edgeWithEndpoints_edge] using hedge

end SerrePositivity.KST.LocalizingInvariants
