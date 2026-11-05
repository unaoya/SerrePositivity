module

public import SerrePositivity.KST.LocalizingInvariants.PullbackStableCategory
public import SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberSquareFamily

/-!
概要：元の lax pullback の指定矢印の cofiber を全単体上の実 ∞ 関手にする。
方針：coherent な普遍四角形の全族を選び、元の通常 pullback と核を同定する。
規約：完全性と商の普遍性は後続工程。使われ方：Tamme の差の項の元の関手。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

/-- 元の指定矢印族に対する cofiber の実関手。 -/
def laxDifference : (laxCategory p q).obj ⟶ E.obj :=
  CofiberFamily.cofiber E.obj (F2.laxPullbackArrow p.hom q.hom)

/-- 差の関手の値を頂点とし、元の指定矢印を底辺とする実普遍四角形。 -/
def laxDifferenceFunctorSquare (x : (laxCategory p q).obj _⦋0⦌) :=
  CofiberFamily.cofiberSquareAt E.obj (F2.laxPullbackArrow p.hom q.hom) x

/-- 既存の頂点ごとの cofiber と、新しい実関手の値の比較。 -/
def laxDifferenceVertexIso (x : (laxCategory p q).obj _⦋0⦌) :
    VertexIso ((laxDifference p q).app (Opposite.op ⦋0⦌) x) (laxDifferenceVertex p q x) :=
  eqToIso (congrArg HomotopyCategory.mk (CofiberFamily.cofiber_vertex E.obj
    (F2.laxPullbackArrow p.hom q.hom) x)) ≪≫
      cofiberSquareComparisonIso (laxDifferenceFunctorSquare p q x) (laxDifferenceSquare p q x)

lemma laxDifference_zero_iff (x : (laxCategory p q).obj _⦋0⦌) :
    IsZeroVertex ((laxDifference p q).app (Opposite.op ⦋0⦌) x) ↔
      F2.IsLaxEquivalenceVertex p.hom q.hom x := by
  change IsZeroVertex ((CofiberFamily.cofiber E.obj (F2.laxPullbackArrow p.hom q.hom)).app _ x) ↔ _
  rw [_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber_vertex]
  exact (laxDifferenceFunctorSquare p q x).homMk_isIso_iff_zero.symm

lemma laxDifference_preservesZero : PreservesZeroVertices (laxDifference p q) := by
  intro x hx
  exact (laxDifference_zero_iff p q x).2 ((laxEquivalenceVertex_stable p q).zero x hx)

lemma laxDifference_kills_pullback (x : (pullbackCategory p q).obj _⦋0⦌) :
    IsZeroVertex (((pullbackInclusion p q).hom ≫ laxDifference p q).app
      (Opposite.op ⦋0⦌) x) :=
  (laxDifference_zero_iff p q _).2 (F2.catPullbackToLax_vertex p.hom q.hom x)

/-- 差の実関手の核は元の完全包含の本質像と一致する。 -/
lemma laxDifference_kernel (x : (laxCategory p q).obj _⦋0⦌) :
    IsZeroVertex ((laxDifference p q).app (Opposite.op ⦋0⦌) x) ↔
      x ∈ essentialImage (pullbackInclusion p q) := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (exists_pullbackVertex_iff p q x).2 ((laxDifference_zero_iff p q x).1 hx)
    exact ⟨y, ⟨eqToIso (congrArg HomotopyCategory.mk hy)⟩⟩
  · rintro ⟨y, ⟨e⟩⟩
    exact (laxDifference_kills_pullback p q y).of_vertexIso (VertexIso.map e (laxDifference p q))

end SerrePositivity.KST.LocalizingInvariants
