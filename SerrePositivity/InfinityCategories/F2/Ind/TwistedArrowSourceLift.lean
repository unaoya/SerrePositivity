module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeEdgewiseRightFibration
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence

/-!
概要：元の right fibration の指定終点上で、全 twisted arrow を一度に持ち上げる。
方針：相対右端比較の自明 Kan 性から一つの全単体の切断を選び、左端を読む。
規約：底の全 twisted arrow と全空間の終点を厳密に保つ。
使われ方：Yoneda の共同 Hom 図式から元の前層への大域的な評価族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {E B : SSet.{u}} (p : E ⟶ B) [RightFibration p]

/-- 全 twisted arrow と同じ終点を保つ、一つの大域的な持ち上げ。 -/
def twistedArrowRightSection :
    pullback (edgewiseRight B) p ⟶ edgewiseSubdivision E :=
  Classical.choose (trivialKanFibration_exists_section (relativeEdgewiseRightComparison p))

/-- 選んだ同じ切断は、元の相対比較の厳密な右逆。 -/
lemma twistedArrowRightSection_comparison :
    twistedArrowRightSection p ≫ relativeEdgewiseRightComparison p = 𝟙 _ :=
  Classical.choose_spec (trivialKanFibration_exists_section (relativeEdgewiseRightComparison p))

/-- 全持ち上げの底は、元の底の twisted arrow そのもの。 -/
lemma twistedArrowRightSection_map :
    twistedArrowRightSection p ≫ edgewiseSubdivisionMap p = pullback.fst (edgewiseRight B) p := by
  rw [← relativeEdgewiseRightComparison_fst p, ← Category.assoc,
    twistedArrowRightSection_comparison, Category.id_comp]

/-- 全持ち上げの右端は、指定した元の全空間の終点そのもの。 -/
lemma twistedArrowRightSection_right :
    twistedArrowRightSection p ≫ edgewiseRight E = pullback.snd (edgewiseRight B) p := by
  rw [← relativeEdgewiseRightComparison_snd p, ← Category.assoc,
    twistedArrowRightSection_comparison, Category.id_comp]

/-- 同じ全族の左端を、反転した元の全空間内で読む。 -/
def twistedArrowSourceLift : pullback (edgewiseRight B) p ⟶ E.op :=
  twistedArrowRightSection p ≫ edgewiseLeft E

/-- 同じ左端評価は、全高次を通じて反転した元の底への射影を保つ。 -/
lemma twistedArrowSourceLift_projection :
    twistedArrowSourceLift p ≫ SSet.opFunctor.map p =
      pullback.fst (edgewiseRight B) p ≫ edgewiseLeft B := by
  rw [twistedArrowSourceLift, Category.assoc, ← edgewiseLeft_naturality,
    ← Category.assoc, twistedArrowRightSection_map]

end SerrePositivity.InfinityCategories.F2.Ind
