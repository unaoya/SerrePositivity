module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ComparisonFiberFunctor

/-!
概要：添字の等式による比較射の導来 fiber の厳密な移送。
方針：等式を恒等式へ帰着し、元の fiber の恒等同型を取る。
規約：底の点も同じ等式で移送する。充填性は不要。
使われ方：HTT 4.2.4.1、coherent nerve の頂点と元の対象の表示の照合。
-/

@[expose] public section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 概要：等しい添字に付随する比較射の導来 fiber は、底の点の移送込みで厳密に同型。
方針：添字の等式を除いて恒等同型へ帰着する。
規約：全空間と底の Kan 性や元の射の fibration 性は要求しない。
使われ方：coherent な錐の頂点を元の単体的圏の対象の頂点で表し直す。 -/
noncomputable def comparisonFiberIndexIso {T : Type v} (E B : T → SSet.{u}) (p : ∀ t, E t ⟶ B t)
    {s t : T} (h : s = t) (b : (B s) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (p s) b ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (p t) (h ▸ b) := by
  cases h
  exact Iso.refl _

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
