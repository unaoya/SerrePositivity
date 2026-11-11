module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.StrictKanPullbackEndComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalReplacementSection
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead

/-!
概要：任意の Kan cospan の end と interval 引き戻しを、左脚置換後の同じ end で比較する。
方針：定値 path の切断の成分ごとの同値性と、一脚 fibration の標準 end 比較を使う。
規約：元の二射に fibration 性を要求しない。使われ方：実模型 fiber 比較への普遍性の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {X Y Z : SSet.{u}} [KanComplex Y] (f : X ⟶ Y) (g : Z ⟶ Y)

/-- 元の任意の cospan から左脚を interval で置換した cospan への厳密な自然変換。 -/
def intervalCospanSSetSection : cospan f g ⟶ cospan (intervalReplacementEndpoint f) g :=
  cospanHomMk (𝟙 Y) (intervalReplacementSection f) (𝟙 Z)
    ((Category.comp_id f).trans (intervalReplacementSection_endpoint f).symm) (by simp)

/-- 元の cospan の end から左脚置換後の同じ end への実際の比較射。 -/
def intervalCospanEndSection :
    HomotopyLimits.bousfieldKanHolim
      ((AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan) ⋙ cospan f g) ⟶
    HomotopyLimits.bousfieldKanHolim
      ((AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan) ⋙
        cospan (intervalReplacementEndpoint f) g) :=
  HomotopyLimits.weightedSectionsMap _
    (Functor.whiskerLeft AsSmall.down (intervalCospanSSetSection f g))

/-- Kan 値では元の定値 path の比較が end の単体的ホモトピー同値を与える。 -/
lemma intervalCospanEndSection_homotopyEquivalence [KanComplex X] [KanComplex Z] :
    IsSimplicialHomotopyEquivalence (intervalCospanEndSection f g) := by
  apply HomotopyLimits.bousfieldKanMap_homotopyEquivalence
  rintro ⟨_ | ⟨_ | _⟩⟩
  · exact HomotopyLimits.homotopyEquivalence_of_isIso (𝟙 Y)
  · have h := intervalReplacementSection_isWeakHomotopyEquivalence f
    exact h.isSimplicialHomotopyEquivalence
  · exact HomotopyLimits.homotopyEquivalence_of_isIso (𝟙 Z)

/-- 元の interval 引き戻しから、同じ左脚置換後の cospan の end への標準比較。 -/
def intervalPullbackEndComparison : intervalPullback f g ⟶
    HomotopyLimits.bousfieldKanHolim
      ((AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan) ⋙
        cospan (intervalReplacementEndpoint f) g) :=
  strictKanPullbackEndComparison (intervalReplacementEndpoint f) g

/-- 任意の Kan cospan の interval 引き戻しは、同じ実比較射で置換後の end と同値。 -/
lemma intervalPullbackEndComparison_homotopyEquivalence [KanComplex X] [KanComplex Z] :
    IsSimplicialHomotopyEquivalence (intervalPullbackEndComparison f g) :=
  strictKanPullbackEndComparison_homotopyEquivalence (intervalReplacementEndpoint f) g

end SerrePositivity.InfinityCategories.F2
