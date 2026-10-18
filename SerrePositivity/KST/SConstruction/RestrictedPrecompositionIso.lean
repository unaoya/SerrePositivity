module
public import SerrePositivity.KST.SConstruction.EquivalenceDiagrams
public import SerrePositivity.InfinityCategories.Core.FunctorCompositionEvaluation

/-! # 全同値図式に制限した前合成の自然同値
概要：添字のホモトピーが各図式の下で可逆な辺になるなら、制限された前合成は関手同型になる。
方針：前合成の辺をパラメーターで評価し、後合成したホモトピーの点ごとの可逆性を使う。
規約：添字内での辺の可逆性は要求しない。使われ方：D(m,w) の評価と定数図式の自然同値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：各図式の下で可逆となる添字のホモトピーは、制限された前合成の関手同型を与える。
方針：各関手頂点で前合成の辺を評価して、後合成したホモトピーの辺と照合する。
規約：パラメーターは任意、標的だけ quasicategory。
使われ方：全同値図式に対する標準単体の収縮の作用。 -/
def restrictedPrecompositionIso {A B C E : SSet.{u}} [Quasicategory C]
    {f g : A ⟶ B} (H : SSet.Homotopy f g) (i : E ⟶ (ihom B).obj C)
    (hH : ∀ (v : E _⦋0⦌) (a : A _⦋0⦌), IsInvertibleEdge (edgeOfSimplex
      (((functorVertexEquiv B C).symm (i.app (Opposite.op ⦋0⦌) v)).app (Opposite.op ⦋1⦌)
        (simplicialHomotopyVertexEdge H a).edge))) :
    FunctorIso (i ≫ (pre f).app C) (i ≫ (pre g).app C) := by
  let q := functorPrecompositionMap A B C
  let q' := q ≫ (pre i).app ((ihom A).obj C)
  let e := functorEdgeOfSimplicialHomotopy H
  have hqv (h : A ⟶ B) : q'.app (Opposite.op ⦋0⦌) (functorVertex h) =
      functorVertex (i ≫ (pre h).app C) := by
    change ((pre i).app ((ihom A).obj C)).app (Opposite.op ⦋0⦌)
      (q.app (Opposite.op ⦋0⦌) (functorVertex h)) = _
    rw [functorPrecompositionMap_vertex]
    rfl
  let m : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom E).obj ((ihom A).obj C)))
      (functorVertex (i ≫ (pre f).app C)) (functorVertex (i ≫ (pre g).app C)) :=
    { edge := q'.app (Opposite.op ⦋1⦌) e.edge
      src_eq := (e.map ((truncation 2).map q')).src_eq.trans (hqv f)
      tgt_eq := (e.map ((truncation 2).map q')).tgt_eq.trans (hqv g) }
  have hm : IsInvertibleEdge m := by
    apply (isInvertibleEdge_iff_evaluateFunctorAt m).2
    intro v
    let u := (functorVertexEquiv B C).symm (i.app (Opposite.op ⦋0⦌) v)
    have hu : functorVertex u = i.app (Opposite.op ⦋0⦌) v :=
      (functorVertexEquiv B C).apply_symm_apply _
    let H' : SSet.Homotopy (f ≫ u) (g ≫ u) := {
      h := H.h ≫ u
      h₀ := by rw [← Category.assoc, H.h₀]; rfl
      h₁ := by rw [← Category.assoc, H.h₁]; rfl
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro z
        exact False.elim z.1.property }
    have hH' : ∀ a, IsInvertibleEdge (simplicialHomotopyVertexEdge H' a).toTruncated := by
      intro a
      exact (isInvertibleEdge_congr
        (e := (simplicialHomotopyVertexEdge H' a).toTruncated)
        (f := edgeOfSimplex (u.app (Opposite.op ⦋1⦌) (simplicialHomotopyVertexEdge H a).edge))
        rfl).2 (hH v a)
    have hinv := functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise H' hH'
    have he : (m.map ((truncation 2).map
        (evaluateFunctorAt (Y := (ihom A).obj C) v))).edge =
        (functorEdgeOfSimplicialHomotopy H').edge := by
      have heval := ConcreteCategory.congr_hom
        (NatTrans.congr_app (stable_pre_evaluateFunctorAt (X := (ihom A).obj C) i v)
          (Opposite.op ⦋1⦌)) (q.app (Opposite.op ⦋1⦌) e.edge)
      change (evaluateFunctorAt v).app (Opposite.op ⦋1⦌)
          (((pre i).app ((ihom A).obj C)).app (Opposite.op ⦋1⦌)
            (q.app (Opposite.op ⦋1⦌) e.edge)) =
        (evaluateFunctorAt (i.app (Opposite.op ⦋0⦌) v)).app (Opposite.op ⦋1⦌)
          (q.app (Opposite.op ⦋1⦌) e.edge) at heval
      change (evaluateFunctorAt v).app (Opposite.op ⦋1⦌)
        (((pre i).app ((ihom A).obj C)).app (Opposite.op ⦋1⦌)
          (q.app (Opposite.op ⦋1⦌) e.edge)) = _
      rw [heval, ← hu]
      have hq := ConcreteCategory.congr_hom
        (NatTrans.congr_app (functorPrecompositionMap_evaluate (A := A) u)
          (Opposite.op ⦋1⦌)) e.edge
      change (evaluateFunctorAt (functorVertex u)).app (Opposite.op ⦋1⦌)
          (q.app (Opposite.op ⦋1⦌) e.edge) =
        ((ihom A).map u).app (Opposite.op ⦋1⦌) e.edge at hq
      rw [hq]
      change ((ihom A).map u).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry H.h)) =
        SSet.yonedaEquiv (curry (H.h ≫ u))
      rw [← SSet.yonedaEquiv_comp, curry_natural_right]
    exact (isInvertibleEdge_congr he).2 hinv
  let := hm
  exact asIso (SSet.Truncated.HomotopyCategory.homMk m)

end SerrePositivity.KST.SConstruction
