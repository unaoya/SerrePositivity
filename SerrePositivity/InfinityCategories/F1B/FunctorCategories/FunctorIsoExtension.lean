module

public import SerrePositivity.InfinityCategories.Core.PrecompositionLifting
public import SerrePositivity.InfinityCategories.Core.EquivalencePathIso

/-!
概要：単射上の指定自然同型を延長し、厳密な制限と延長ホモトピーを保持する。
方針：可逆 path の始点射影の trivial Kan fibration による持ち上げを使う。
規約：指定同型の代表ホモトピーを部分図式上でそのまま保持する。
使われ方：相対 join の両端の厳密化と指定自然変換の類の追跡。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：単射上の同型を延長した厳密化の証明データ。
方針：新図式だけでなく、元の図式からの可逆ホモトピーを全時間で記録する。
規約：時間は第一因子、部分図式上のホモトピーは指定同型の選んだ代表に等しい。
使われ方：両端の図式の変更と、その間の自然変換の coherence を同時に追跡する。 -/
structure FunctorIsoExtension {A B D : SSet.{u}} [Quasicategory D]
    (i : A ⟶ B) (u : B ⟶ D) (v : A ⟶ D) (e : FunctorIso (i ≫ u) v) where
  diagram : B ⟶ D
  restriction : i ≫ diagram = v
  homotopy : (Δ[1] : SSet.{u}) ⊗ B ⟶ D
  start : prismEndpoint 0 B ≫ homotopy = u
  finish : prismEndpoint 1 B ≫ homotopy = diagram
  fixed : (Δ[1] ◁ i) ≫ homotopy =
    (β_ (Δ[1] : SSet.{u}) A).hom ≫ (FunctorIso.simplicialHomotopy e).h
  invertible : ∀ x : B _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
    (homotopy.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)))

/-- 概要：単射上の自然同型は、厳密な制限と可逆ホモトピーを保持して延長できる。
方針：指定同型を代表するホモトピーを可逆 path として持ち上げる。
規約：D のみ quasicategory、i は単射。
使われ方：元の端点比較を保持した図式の厳密化。 -/
lemma functorIsoExtension_nonempty {A B D : SSet.{u}} [Quasicategory D]
    (i : A ⟶ B) [Mono i] (u : B ⟶ D) (v : A ⟶ D) (e : FunctorIso (i ≫ u) v) :
    Nonempty (FunctorIsoExtension i u v e) := by
  let H := FunctorIso.simplicialHomotopy e
  let J := (β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h
  have h₀ : prismEndpoint 0 A ≫ J = i ≫ u := by
    rw [← Category.assoc, prismEndpoint_zero_braiding]
    exact H.h₀
  have h₁ : prismEndpoint 1 A ≫ J = v := by
    rw [← Category.assoc, prismEndpoint_one_braiding]
    exact H.h₁
  have hv : ∀ x : A _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
      (J.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))) := by
    intro x
    have he : J.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1) =
        (simplicialHomotopyVertexEdge H x).edge := by
      change H.h.app (Opposite.op ⦋1⦌)
        (PinchedHom.constant x 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
        H.h.app (Opposite.op ⦋1⦌)
          ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) x).edge, homotopyIntervalEdge.edge)
      have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
        apply stdSimplex.ext
        intro j
        fin_cases j <;> rfl
      rw [pinchedConstant_one, hi]
    exact (isInvertibleEdge_congr he).2
      (simplicialHomotopyOfFunctorEdge_vertex_isInvertible
        (FunctorIso.edge e) (FunctorIso.edge_isInvertible e) x)
  obtain ⟨L, hL, hL₀, hLv⟩ := equivalenceHomotopy_extend i J u h₀ hv
  have hL₁ : i ≫ (prismEndpoint 1 B ≫ L) = v := by
    rw [← Category.assoc, ← prismEndpoint_naturality, Category.assoc, hL, h₁]
  exact ⟨{
    diagram := prismEndpoint 1 B ≫ L
    restriction := hL₁
    homotopy := L
    start := hL₀
    finish := rfl
    fixed := hL
    invertible := hLv }⟩

/-- 概要：厳密化の新図式は元の図式と関手圏内で同型。
方針：保持したホモトピーの全頂点での可逆性を使う。
規約：単なる各点の同型の族ではない。
使われ方：厳密化前後の図式の大域的比較。 -/
def FunctorIsoExtension.globalIso {A B D : SSet.{u}} [Quasicategory D]
    {i : A ⟶ B} {u : B ⟶ D} {v : A ⟶ D} {e : FunctorIso (i ≫ u) v}
    (s : FunctorIsoExtension i u v e) : FunctorIso u s.diagram := by
  have h := functorIsoOfEquivalenceHomotopy s.homotopy s.invertible
  rw [s.start, s.finish] at h
  exact h

end SerrePositivity.InfinityCategories
