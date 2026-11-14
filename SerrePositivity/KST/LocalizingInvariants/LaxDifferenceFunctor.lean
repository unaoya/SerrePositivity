module

public import SerrePositivity.KST.LocalizingInvariants.PullbackStableCategory
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

/-- 元の指定矢印族に対する cofiber の実関手。 -/
def laxDifference : (laxCategory p q).obj ⟶ E.obj :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber E.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p.hom q.hom)

/-- 差の関手の値を頂点とし、元の指定矢印を底辺とする実普遍四角形。 -/
def laxDifferenceFunctorSquare (x : (laxCategory p q).obj _⦋0⦌) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiberSquareAt E.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p.hom q.hom) x

/-- 既存の頂点ごとの cofiber と、新しい実関手の値の比較。 -/
def laxDifferenceVertexIso (x : (laxCategory p q).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((laxDifference p q).app (Opposite.op ⦋0⦌) x) (laxDifferenceVertex p q x) :=
  eqToIso (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber_vertex E.obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p.hom q.hom) x)) ≪≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSquareComparisonIso (laxDifferenceFunctorSquare p q x) (laxDifferenceSquare p q x)

lemma laxDifference_zero_iff (x : (laxCategory p q).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((laxDifference p q).app (Opposite.op ⦋0⦌) x) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsLaxEquivalenceVertex p.hom q.hom x := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber E.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p.hom q.hom)).app _ x) ↔ _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber_vertex]
  exact (laxDifferenceFunctorSquare p q x).homMk_isIso_iff_zero.symm

lemma laxDifference_preservesZero : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesZeroVertices (laxDifference p q) := by
  intro x hx
  exact (laxDifference_zero_iff p q x).2 ((laxEquivalenceVertex_stable p q).zero x hx)

lemma laxDifference_kills_pullback (x : (pullbackCategory p q).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((pullbackInclusion p q).hom ≫ laxDifference p q).app
      (Opposite.op ⦋0⦌) x) :=
  (laxDifference_zero_iff p q _).2 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackToLax_vertex p.hom q.hom x)

/-- 差の実関手の核は元の完全包含の本質像と一致する。 -/
lemma laxDifference_kernel (x : (laxCategory p q).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((laxDifference p q).app (Opposite.op ⦋0⦌) x) ↔
      x ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (pullbackInclusion p q) := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (exists_pullbackVertex_iff p q x).2 ((laxDifference_zero_iff p q x).1 hx)
    exact ⟨y, ⟨eqToIso (congrArg HomotopyCategory.mk hy)⟩⟩
  · rintro ⟨y, ⟨e⟩⟩
    exact (laxDifference_kills_pullback p q y).of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (laxDifference p q))

end SerrePositivity.KST.LocalizingInvariants
