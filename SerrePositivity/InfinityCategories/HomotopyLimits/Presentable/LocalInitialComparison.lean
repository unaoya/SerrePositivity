module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Core.InnerFiber
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.LeftFiberKan
public import SerrePositivity.InfinityCategories.Core.MappingSpaceLeft
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.F1.LeftFibrationInitialHomComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.LocalCoslicePrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.LocalObjects
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeFiberPrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.EdgeCosliceIntervalMap
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialRestrictionBaseEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialRestrictionHomSquare
public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftFibrationInitialSpan

/-!
概要：始対象間の元の比較辺の局所性を、底上の関手の fiber の同値性から導く。
方針：全 Hom の比較のホモトピー可換性と同値の二対三則を使う。
規約：元の比較辺と余極限余錐を保持。使われ方：HTT 5.5.4.5(2) の余極限閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 底上の関手の指定比較辺への局所性は、元の左 Hom の前合成の同値性と一致。 -/
lemma isLocalForHom_initialRestriction_iff_precomposition {E F B : SSet.{u}}
    [Quasicategory B] (p : E ⟶ B) (q : F ⟶ B) (r : E ⟶ F) (hr : r ≫ q = p)
    (d : E _⦋0⦌) {c : F _⦋0⦌} (e : F.Edge c (r.app (Opposite.op ⦋0⦌) d))
    (z : B _⦋0⦌) :
    IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk
      (edgeCosliceEdge (SSet.yonedaEquiv.symm e.edge ≫ q))) z ↔
      IsQCatEquivalence (initialRestrictionHomPrecomposition p q r hr d e z) := by
  rw [isLocalForHom_edge_iff_coslicePrecomposition
    (SSet.yonedaEquiv.symm e.edge ≫ q) (SSet.yonedaEquiv.symm c ≫ q)
    (SSet.yonedaEquiv.symm d ≫ p)
    (by rw [← Category.assoc, e.δ_one_yonedaEquiv_symm])
    (initialRestrictionEdgeBase_eq p q r hr d e).symm]
  have hs : IsQCatEquivalence (leftFibrationInitialBaseIso p d z).inv :=
    (qCatEquivalenceOfIso (leftFibrationInitialBaseIso p d z).symm).isQCatEquivalence
  have ht : IsQCatEquivalence (leftFibrationInitialBaseIso q c z).hom :=
    (qCatEquivalenceOfIso (leftFibrationInitialBaseIso q c z)).isQCatEquivalence
  constructor
  · intro h
    exact hs.comp (h.comp ht)
  · intro h
    exact ht.cancel_right (hs.cancel_left h)

/-- 始対象間の指定した比較辺の底への像は、対応する fiber 制限が同値なら局所。 -/
lemma isLocalForHom_initialRestriction_of_fiber_equivalence {E F B : SSet.{u}}
    [Quasicategory B] (p : E ⟶ B) [LeftFibration p] (q : F ⟶ B) [LeftFibration q]
    (r : E ⟶ F) (hr : r ≫ q = p) (d : E _⦋0⦌) (hd : IsInitialVertex d)
    {c : F _⦋0⦌} (hc : IsInitialVertex c)
    (e : F.Edge c (r.app (Opposite.op ⦋0⦌) d)) (z : B _⦋0⦌)
    (h : IsQCatEquivalence (vertexFiberMap p q r hr z)) :
    IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk
      (edgeCosliceEdge (SSet.yonedaEquiv.symm e.edge ≫ q))) z := by
  apply (isLocalForHom_initialRestriction_iff_precomposition p q r hr d e z).mpr
  have hs := (leftFibrationInitialHomComparison_homotopyEquivalence p d hd z).isQCatEquivalence
  have ht := (leftFibrationInitialHomComparison_homotopyEquivalence q c hc z).isQCatEquivalence
  obtain ⟨H⟩ := initialRestrictionHomComparison_square p q r hr d hd e z hc
  exact hs.cancel_left ((h.comp ht).ofFunctorIso (functorIsoOfSimplicialHomotopy H))

end SerrePositivity.InfinityCategories.HomotopyLimits
