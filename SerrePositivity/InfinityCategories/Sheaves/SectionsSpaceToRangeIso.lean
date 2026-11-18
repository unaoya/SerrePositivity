module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsRangeCechComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.SpacePresentable

/-!
概要：像への射に沿う空間値の指定切断の写像は可逆。
方針：元の指定切断の辺をホモトピー圏で比較する。
  文献対応：HTT 6.2.2.6（集合値前層の局所同値の場合）。
使われ方：一般の層の係数に対する切断の局所性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open Truncated.HomotopyCategory

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 像への射に沿う空間値の指定切断の写像は可逆。 -/
@[cite HTT "6.2.2.6" (partial := special) "小さい通常の site の集合値前層と空間値の切断。"]
lemma sections_toRange_isInvertible_space :
∀ {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
 {P Q : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q)
 [CategoryTheory.Presheaf.IsLocallyInjective J f]
 (O : Presheaf C SpaceInfinity.{u}) (hO : IsSheaf J O)
 (hP : HasLimit (sectionsOfDiagram P O))
 (hR : HasLimit (sectionsOfDiagram (Subfunctor.range f).toFunctor O)),
 IsInvertibleEdge (sectionsOf_map (Subfunctor.toRange f) O hP hR).toTruncated := by
  intro C hC J P Q f hf O hO hP hR
  let hE := space_isPresentable.{u}
  let R := (Subfunctor.range f).toFunctor
  let g : P ⟶ R := Subfunctor.toRange f
  let e := (nerve.edgeMk g).map (discretePresheafInclusion C).val
  let r := (edgeOp e.toTruncated).map ((truncation 2).map (weightedSections O hE))
  let eP := (weightedSections_discrete O hE P hP).hom
  let eR := (weightedSections_discrete O hE R hR).hom
  let m := homMk (sectionsOf_map g O hP hR).toTruncated
  letI : IsIso (homMk r) := weightedSections_toRangeHom_isInvertible J f O hO hE
  letI : IsIso eP := inferInstanceAs (IsIso (weightedSections_discrete O hE P hP).hom)
  letI : IsIso eR := inferInstanceAs (IsIso (weightedSections_discrete O hE R hR).hom)
  have hr : homMk r ≫ eP = eR ≫ m := weightedSections_discrete_map O hE g hP hR
  have hm : IsIso (eR ≫ m) := hr ▸ inferInstanceAs (IsIso (homMk r ≫ eP))
  exact (isIso_comp_left_iff eR m).mp hm

end SerrePositivity.InfinityCategories.Sheaves
