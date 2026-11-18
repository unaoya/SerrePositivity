module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLanePoints
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DoldKanIso

/-!
# 指定 Dold–Kan 段の Kan 性

DAG XIII §2.2 の Eilenberg–Mac Lane の段を、単位からの dg Hom の Γ と比較する。
既存の N4 の直接の線形充填を再利用し、単体的加群の Kan 性を仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 単位からの dg Hom と同じ段の複体の同型を、実 Γ へ送る。 -/
def levelHomSpaceIso (M : Complex A) (n : ℕ) :
    DifferentialGradedCategories.doldKanHomSpace
      (R := A) (𝟙_ (Complex A)) ((shiftFunctor (Complex A) (n : ℤ)).obj M) ≅
        (levelSpaceFunctor A n).obj M :=
  (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).mapIso
    (MonoidalClosed.unitIsoSelf (C := Complex A)
      (X := (shiftFunctor (Complex A) (n : ℤ)).obj M))

open SSet.modelCategoryQuillen in
/-- Γ の指定段は、単位からの Hom の線形充填により Kan である。 -/
instance levelSpaceKan (M : Complex A) (n : ℕ) :
    SSet.KanComplex ((levelSpaceFunctor A n).obj M) :=
  HomotopicalAlgebra.isFibrant_of_fibration (levelHomSpaceIso A M n).inv

end SerrePositivity.EInfinity.PowerOperation
