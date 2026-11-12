module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Localization
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise

/-!
概要：関手圏への後合成が反転する辺は、各頂点で反転される辺と厳密に一致する。
方針：全ての関手頂点を表示して点ごとの可逆性判定を使い、評価と後合成を交換する。
規約：パラメーターは任意の単体集合。使われ方：矢印圏上の元の分母の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

def pointwiseLocalizingEdges (K X : SSet.{u}) (W : Set (X _⦋1⦌)) :
    Set (((ihom K).obj X) _⦋1⦌) :=
  {s | ∀ k : K _⦋0⦌, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k).app (Opposite.op ⦋1⦌) s ∈ W}

lemma isInvertibleFunctorEdge_iff_evaluations {K X : SSet.{u}} [Quasicategory X]
    {x y : ((ihom K).obj X) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X)) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e ↔ ∀ k : K _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k))) := by
  obtain ⟨f, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K X).surjective x
  obtain ⟨g, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K X).surjective y
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt e

lemma invertedEdges_ihom_map {X Q : SSet.{u}} [Quasicategory Q]
    (K : SSet.{u}) (F : X ⟶ Q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges ((ihom K).map F) = pointwiseLocalizingEdges K X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F) := by
  ext s
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom K).obj Q)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s).map ((truncation 2).map ((ihom K).map F))) ↔ _
  rw [isInvertibleFunctorEdge_iff_evaluations (K := K) (X := Q)]
  apply forall_congr'
  intro k
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr rfl

lemma pointwiseLocalizingEdges_mono {K X : SSet.{u}} {W V : Set (X _⦋1⦌)}
    (h : W ⊆ V) : pointwiseLocalizingEdges K X W ⊆ pointwiseLocalizingEdges K X V :=
  fun _ hs k => h (hs k)

end SerrePositivity.KST.LocalizingInvariants
