module

public import SerrePositivity.EInfinity.BarrattEccles.FreeNormalizedHomUnit
public import SerrePositivity.EInfinity.BarrattEccles.FreeNormalizedHomEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomotopyIsoTransport

/-!
# 元の標準自由 Hom と実 DK Hom から同じ共通 Hom への実弱 span

概要：元の QX と標的の実底を持つ DK Hom を、同じ共通 Hom へ全自然に送る。
方針：同じ全随伴・DK 同型の逆と、証明済みの正規化比較射を合成する。
規約：標準 sourceFrameHom と実 Γ の Hom を保つ。
使われ方：標準自由単位誘導射と元の D(R) Hom 比較の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

def freeNormalizedHomFromDoldKan :
    ((ComplexLimits.framedLimitProbeFunctor A).op ⋙
      ComplexLimits.actualDoldKanHomBifunctor A) ⋙
        (Functor.whiskeringLeft (operad A).Algebra (Complex A) SSet.{u}).obj
          (Operad.Algebra.forget (operad A)) ⟶ freeNormalizedHomMiddle A :=
  (freeNormalizedProbeDoldKanIso A).inv ≫ freeNormalizedHomFromTensor A

open SSet.modelCategoryQuillen in
lemma freeNormalizedHomFromDoldKan_homotopyEquivalence
    (X : (Complex A)ᵒᵖ) (B : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (((freeNormalizedHomFromDoldKan A).app X).app B) := by
  have := freeNormalizedProbeHom_kanComplex A X B
  have := freeNormalizedHomMiddle_kanComplex A X B
  have : KanComplex (((((ComplexLimits.framedLimitProbeFunctor A).op ⋙
      ComplexLimits.actualDoldKanHomBifunctor A) ⋙
        (Functor.whiskeringLeft (operad A).Algebra (Complex A) SSet.{u}).obj
          (Operad.Algebra.forget (operad A))).obj X).obj B) :=
    HomotopicalAlgebra.isFibrant_of_fibration
      (((freeNormalizedProbeDoldKanIso A).inv.app X).app B)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialHomotopyEquivalence_iso_hom
    (((freeNormalizedProbeDoldKanIso A).app X).app B).symm).comp
    (freeNormalizedHomFromTensor_homotopyEquivalence A X B)

end SerrePositivity.EInfinity.BarrattEccles
