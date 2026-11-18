module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsContinuity
public import SerrePositivity.InfinityCategories.Sheaves.PresheafRelativeCechColimit
public import SerrePositivity.InfinityCategories.Sheaves.LocalEquivalenceImageReduction

/-!
概要：点ごとに全射な集合値前層の同じ Čech 増大余錐を、元の全切断関手で極限錐へ送る。
方針：既証の全余錐の余極限性を、小余極限を反転する同じ右 Kan 延長へ渡す。
規約：HTT 5.1.5.6 の双対の特殊化。元の図式、増大、全切断関手を保持する。
使われ方：S8 の局所同値の Čech 解消と定値錐の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u}
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の Čech 全増大余錐は、指定した全切断関手で極限錐に写る。 -/
@[cite HTT "5.1.5.6" (partial := special)
  "小さい通常の site の集合値前層の点ごとに全射な射の Čech 増大の切断に特殊化する。"]
lemma weightedSections_relativeCech_isLimit (f : P ⟶ Q)
    (hf : ∀ X : Cᵒᵖ, Function.Surjective (f.app X)) (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    IsLimitCone (mapJoinCone (weightedSections O hE)
      (coconeReverseCone (discretePresheafCocone (relativeCechCocone f)))) :=
  sectionsOf_colimit O hE _ (presheafRelativeCechCocone_isColimit f hf)

/-- 任意の射の像への同じ全射の Čech 増大に対する指定切断の極限性。 -/
lemma weightedSections_rangeCech_isLimit (f : P ⟶ Q) (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    IsLimitCone (mapJoinCone (weightedSections O hE)
      (coconeReverseCone (discretePresheafCocone (relativeCechCocone (Subfunctor.toRange f))))) :=
  weightedSections_relativeCech_isLimit (Subfunctor.toRange f) (toRange_app_surjective f) O hE

end SerrePositivity.InfinityCategories.Sheaves
