module

public import SerrePositivity.KST.LocalizingInvariants.SimplexAttachmentComparisons
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.F1.SuspensionDiagramArrows

/-!
概要：前段と次辺の元の比較が可逆なら、貼り合わせた全図式の比較も可逆。
方針：join の全頂点を二因子で尽くし、指定された同じ比較辺を各頂点で判定する。
規約：全図式の実比較辺を先に構成し、その辺自身の可逆性を証明する。
使われ方：c5 の有限線型図式の帰納的持ち上げで全 FunctorIso を貼る工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

private lemma join_vertex_cases {A B : SSet.{u}} (v : (join A B) _⦋0⦌) :
    (∃ a, (joinInl A B).app (Opposite.op ⦋0⦌) a = v) ∨
      ∃ b, (joinInr A B).app (Opposite.op ⦋0⦌) b = v := by
  rcases v with ⟨ℓ, a, b⟩
  fin_cases ℓ
  · right
    cases a
    exact ⟨b, rfl⟩
  · left
    cases b
    exact ⟨a, rfl⟩

private lemma invertible_at_pre {K L X : SSet.{u}} [Quasicategory X]
    (j : K ⟶ L) {F G : L ⟶ X}
    (e : Truncated.Edge (X := (truncation 2).obj ((ihom L).obj X))
      (functorVertex F) (functorVertex G))
    (he : IsInvertibleEdge (X := (ihom K).obj X)
      (e.map ((truncation 2).map ((pre j).app X)))) (k : K _⦋0⦌) :
    IsInvertibleEdge (e.map ((truncation 2).map
      (evaluateFunctorAt (Y := X) (j.app (Opposite.op ⦋0⦌) k)))) := by
  have hm := he.map (evaluateFunctorAt (Y := X) k)
  have hcomp := ConcreteCategory.congr_hom (NatTrans.congr_app
    (stable_pre_evaluateFunctorAt (X := X) j k) (Opposite.op ⦋1⦌)) e.edge
  exact (isInvertibleEdge_congr hcomp).mp hm

/-- 指定された全比較辺は、前段と次辺への制限が可逆ならそれ自身が可逆。 -/
lemma simplexAttachmentComparison_isInvertible {X : SSet.{u}} [Quasicategory X]
    (n : ℕ) {F G : join (Δ[n] : SSet.{u}) Δ[0] ⟶ X}
    (l : Truncated.Edge
      (X := (truncation 2).obj ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj X))
      (functorVertex F) (functorVertex G))
    (ha : IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj X)
      (l.map ((truncation 2).map ((pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app X))))
    (hb : IsInvertibleEdge (X := (ihom (join (Δ[0] : SSet.{u}) Δ[0])).obj X)
      (l.map ((truncation 2).map
        ((pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app X)))) :
    IsInvertibleEdge (X := (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj X) l := by
  apply (isInvertibleEdge_iff_evaluateFunctorAt l).mpr
  intro v
  rcases join_vertex_cases v with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact invertible_at_pre (joinInl Δ[n] Δ[0]) l ha k
  · let u := (joinInr (Δ[0] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌) k
    have hu : (joinMap (simplexLastPoint n) (𝟙 Δ[0])).app (Opposite.op ⦋0⦌) u =
        (joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌) k := by
      have hh : joinInr (Δ[0] : SSet.{u}) Δ[0] ≫
          joinMap (simplexLastPoint n) (𝟙 Δ[0]) = joinInr (Δ[n] : SSet.{u}) Δ[0] := by
        simpa only [Category.id_comp] using
          joinInr_joinMap (simplexLastPoint n) (𝟙 (Δ[0] : SSet.{u}))
      exact ConcreteCategory.congr_hom (C := Type u)
        (NatTrans.congr_app hh (Opposite.op ⦋0⦌)) k
    rw [← hu]
    exact invertible_at_pre (joinMap (simplexLastPoint n) (𝟙 Δ[0])) l hb u

/-- 指定された二つの可逆比較を、元の両制限の順方向の射を保つ全 FunctorIso へ貼る。 -/
lemma exists_simplexAttachmentFunctorIso {X : SSet.{u}} [Quasicategory X] (n : ℕ)
    (F G : join (Δ[n] : SSet.{u}) Δ[0] ⟶ X)
    (a : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj X))
      (functorVertex (joinInl Δ[n] Δ[0] ≫ F)) (functorVertex (joinInl Δ[n] Δ[0] ≫ G)))
    (b : Truncated.Edge
      (X := (truncation 2).obj ((ihom (join (Δ[0] : SSet.{u}) Δ[0])).obj X))
      (functorVertex (joinMap (simplexLastPoint n) (𝟙 Δ[0]) ≫ F))
      (functorVertex (joinMap (simplexLastPoint n) (𝟙 Δ[0]) ≫ G)))
    (hab : SSet.yonedaEquiv.symm a.edge ≫ (pre (simplexLastPoint n)).app X =
      SSet.yonedaEquiv.symm b.edge ≫ (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app X)
    (ha : IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj X) a)
    (hb : IsInvertibleEdge (X := (ihom (join (Δ[0] : SSet.{u}) Δ[0])).obj X) b) :
    ∃ e : FunctorIso F G,
      Arrow.mk ((hoFunctor.map ((pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app X)).toFunctor.map
        e.hom) = Arrow.mk (Truncated.HomotopyCategory.homMk a) ∧
      Arrow.mk ((hoFunctor.map
        ((pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app X)).toFunctor.map e.hom) =
          Arrow.mk (Truncated.HomotopyCategory.homMk b) := by
  obtain ⟨l, hl, hr⟩ := exists_simplexAttachmentComparison n F G a b hab
  have hla : IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj X)
      (l.map ((truncation 2).map ((pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app X))) :=
    (isInvertibleEdge_congr hl).mpr ha
  have hlb : IsInvertibleEdge (X := (ihom (join (Δ[0] : SSet.{u}) Δ[0])).obj X)
      (l.map ((truncation 2).map
        ((pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app X))) :=
    (isInvertibleEdge_congr hr).mpr hb
  have := simplexAttachmentComparison_isInvertible n l hla hlb
  refine ⟨asIso (Truncated.HomotopyCategory.homMk l), ?_, ?_⟩
  · exact Truncated.HomotopyCategory.congr_arrowMk_homMk _ a hl
  · exact Truncated.HomotopyCategory.congr_arrowMk_homMk _ b hr

end SerrePositivity.KST.LocalizingInvariants
