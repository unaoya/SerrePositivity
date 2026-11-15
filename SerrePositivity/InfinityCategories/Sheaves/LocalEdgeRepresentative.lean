module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalObjects

/-!
概要：同じ一単体から復元した辺で局所性を試しても、元の辺での局所性と一致する。
方針：辺の端点の等式を除去して同じHomとなることを確認する。
使われ方：HTT 5.5.4.1、Kerodon Tag 06VH の生成辺族の局所性。
規約：辺の代表を変える際の計算則。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
namespace SerrePositivity.InfinityCategories.Sheaves

/-- 端点を一単体の面で読むか、元の指定端点で読むかに局所性は依存しない。 -/
lemma localForEdgeRepresentative_iff {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : X.Edge x y) (z : X _⦋0⦌) :
    IsLocalForHom (Truncated.HomotopyCategory.homMk (edgeOfSimplex e.edge)) z ↔
      IsLocalForHom (Truncated.HomotopyCategory.homMk e.toTruncated) z := by
  rcases e with ⟨s, hs, ht⟩
  subst x
  subst y
  rfl

end SerrePositivity.InfinityCategories.Sheaves
