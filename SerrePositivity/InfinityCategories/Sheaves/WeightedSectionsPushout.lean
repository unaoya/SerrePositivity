module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsContinuity
public import SerrePositivity.InfinityCategories.Sheaves.DiscretePushoutSquareComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.DensityConeOppositeRestriction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorVertexConeReindex

/-!
概要：集合値前層の単射に沿う指定押し出しを、元の全切断関手で引き戻しへ送る。
方針：HTT 5.1.5.6 の双対による小余極限の反転を、既存の span の形状同型で戻す。
規約：元の指定四角形とその全余錐を保持し、形状の宇宙を省略しない。
使われ方：集合値の商に対する切断の引き戻し。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Project.FilteredExchange
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
  (O : Presheaf C E)
  (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)

/-- 小さい形状と実際に同型な形状でも、同じ指定余錐の切断は極限錐。
形状制限と余錐反転の既存の全射の等式で移す。 -/
lemma sectionsOf_colimit_of_shapeIso {I : SSet.{u}} {J : SSet.{u + 1}}
    (e : (SSet.uliftFunctor.{u + 1, u}).obj I ≅ J)
    {p : J ⟶ PresheafCat C SpaceInfinity.{u}} (c : JoinCocone p) (hc : IsColimitCone c) :
    IsLimitCone (mapJoinCone (weightedSections O hE) (coconeReverseCone c)) := by
  have hr := sectionsOf_colimit O hE (c.restrict e.hom)
    ((isColimitCone_iff_restrict_of_isIso c e.hom).mp hc)
  apply (isLimitCone_restrict_iff_of_isIso
    (mapJoinCone (weightedSections O hE) (coconeReverseCone c))
      (SSet.opFunctor.map e.hom)).mp
  apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).mp hr
  change (coconeReverseCone (c.restrict e.hom)).val ≫ weightedSections O hE =
    joinMap (𝟙 Δ[0]) (SSet.opFunctor.map e.hom) ≫
      ((coconeReverseCone c).val ≫ weightedSections O hE)
  rw [← Category.assoc, coconeReverseCone_restrict_val]

/-- 単射に沿う集合値前層の元の押し出し余錐を、同じ全切断関手は極限錐へ送る。
HTT 5.1.5.6 の双対と、離散空間の単射に沿う押し出しの特殊化。 -/
@[cite HTT "5.1.5.6" (partial := special)
  "小さい通常の site の集合値前層の単射に沿う指定押し出しの切断に特殊化する。"]
theorem sectionsOf_pushout {P Q R : Cᵒᵖ ⥤ Type u} (f : P ⟶ Q) (g : P ⟶ R) [Mono f]
    (O : Presheaf C E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    IsLimitCone (mapJoinCone (weightedSections O hE)
      (coconeReverseCone (pushoutCocone (discretePushoutSquare f g)))) :=
  sectionsOf_colimit_of_shapeIso O hE (strictSpanHornIso.{u, u + 1}) _
    (discretePushoutSquare_isPushout f g)

end SerrePositivity.InfinityCategories.Sheaves
