module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConePostcomposeBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RightKanLimitComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.FunctorHomCongrEvaluation

/-!
概要：通常の錐の制限と指定三角形を、元の全錐間の変換として極限比較へ接続する。
方針：既存の nerveCone_whisker と後合成の全ホモトピーを再利用し、端点だけを輸送する。
使われ方：Kerodon §7.1（Tag 02H1）、HTT 6.2.2.6 の篩の二段分解。
規約：指定自然変換と元の係数を保ち、この中間判定では極限存在を明示する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
variable {I J C : Type u} [Category.{u} I] [Category.{u} J] [Category.{u} C]

/-- 通常の錐を制限してから同じ係数へ写しても、元の全錐の制限と同じ全射を得る。 -/
lemma nerveConeWhiskerPostcompose_val (δ : I ⥤ J) {P : J ⥤ C} (c : Cone P)
    {X : SSet.{u}} (U : nerve C ⟶ X) :
    (mapJoinCone U (nerveCone (c.whisker δ))).val =
      (restrictJoinCone (mapJoinCone U (nerveCone c)) (nerveMap δ)).val := by
  change (nerveCone (c.whisker δ)).val ≫ U =
    joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap δ) ≫ (nerveCone c).val ≫ U
  rw [← nerveCone_whisker, Category.assoc]

/-- 同じ通常の三角形を、元の制限錐からの全変換として使用する。 -/
def nerveConeWhiskerPostcomposeHom (δ : I ⥤ J) {P : J ⥤ C} {Q : I ⥤ C}
    (c : Cone P) (η : δ ⋙ P ⟶ Q) {X : SSet.{u}} (U : nerve C ⟶ X) :
    FunctorHom (restrictJoinCone (mapJoinCone U (nerveCone c)) (nerveMap δ)).val
      (mapJoinCone U (nerveCone ((Cone.postcompose η).obj (c.whisker δ)))).val :=
  kanFunctorHomCongr (nerveConeWhiskerPostcompose_val δ c U) rfl
    (nerveConePostcomposeHom (c.whisker δ) η U)

/-- 全錐の変換の頂点成分は、同じ元の後合成の変換から来て可逆。 -/
lemma nerveConeWhiskerPostcomposeHom_apex_isIso (δ : I ⥤ J)
    {P : J ⥤ C} {Q : I ⥤ C} (c : Cone P) (η : δ ⋙ P ⟶ Q)
    {X : SSet.{u}} (U : nerve C ⟶ X) :
    IsIso (functorHomEvaluate (nerveConeWhiskerPostcomposeHom δ c η U)
      (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) (nerve I)))) := by
  apply (kanFunctorHomCongr_evaluate_isIso_iff _ _ _ _).mpr
  exact nerveConePostcomposeHom_apex_isIso (c.whisker δ) η U

/-- 元の通常の合成図式を nerve と同じ係数へ写すと、同じ前合成に等しい。 -/
lemma nerveWhiskerCoefficient_eq (δ : I ⥤ J) (P : J ⥤ C)
    {X : SSet.{u}} (U : nerve C ⟶ X) :
    nerveMap (δ ⋙ P) ≫ U = nerveMap δ ≫ (nerveMap P ≫ U) := by
  have h : nerveMap (δ ⋙ P) = nerveMap δ ≫ nerveMap P :=
    nerveFunctor.map_comp δ.toCatHom P.toCatHom
  rw [h, Category.assoc]

/-- 制限錐からの全変換の底は、元の三角形の同じ指定射へ正規化される。 -/
lemma nerveConeWhiskerPostcomposeHom_boundary (δ : I ⥤ J)
    {P : J ⥤ C} {Q : I ⥤ C} (c : Cone P) (η : δ ⋙ P ⟶ Q)
    {X : SSet.{u}} (U : nerve C ⟶ X) :
    kanFunctorHomCongr
      (restrictJoinCone (mapJoinCone U (nerveCone c)) (nerveMap δ)).property
      (mapJoinCone U (nerveCone ((Cone.postcompose η).obj (c.whisker δ)))).property
      ((hoFunctor.map ((pre (joinInr (Δ[0] : SSet.{u}) (nerve I))).app X)).toFunctor.map
        (nerveConeWhiskerPostcomposeHom δ c η U)) =
      kanFunctorHomCongr (nerveWhiskerCoefficient_eq δ P U) rfl
        (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
          (functorHomotopyPostcomp (nerveNatTransHomotopy η) U))) := by
  apply Arrow.mk_injective
  rw [kanFunctorHomCongr_arrow, kanFunctorHomCongr_arrow]
  change (hoFunctor.map ((pre (joinInr (Δ[0] : SSet.{u}) (nerve I))).app X)).toFunctor.mapArrow.obj
    (Arrow.mk (nerveConeWhiskerPostcomposeHom δ c η U)) = _
  rw [nerveConeWhiskerPostcomposeHom, kanFunctorHomCongr_arrow]
  have h := congrArg Arrow.mk (nerveConePostcomposeHom_boundary (c.whisker δ) η U)
  rw [kanFunctorHomCongr_arrow] at h
  exact h

/-- 存在する極限を使った場合、元の通常の三角形の右 Kan 条件で二つの全錐を比較できる。 -/
lemma nerveConeWhiskerPostcompose_isLimit_iff (δ : I ⥤ J)
    {P : J ⥤ C} {Q : I ⥤ C} (c : Cone P) (η : δ ⋙ P ⟶ Q)
    {X : SSet.{u}} [Quasicategory X] (U : nerve C ⟶ X)
    (hp : HasLimit (nerveMap P ≫ U)) (hq : HasLimit (nerveMap Q ≫ U))
    (hη : RightKanHomUniversal (nerveMap δ)
      (kanFunctorHomCongr (nerveWhiskerCoefficient_eq δ P U) rfl
        (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
          (functorHomotopyPostcomp (nerveNatTransHomotopy η) U))))) :
    IsLimitCone (mapJoinCone U (nerveCone c)) ↔
      IsLimitCone (mapJoinCone U (nerveCone ((Cone.postcompose η).obj (c.whisker δ)))) := by
  haveI := nerveConeWhiskerPostcomposeHom_apex_isIso δ c η U
  apply isLimitCone_iff_of_rightKan_comparison_with_limits (nerveMap δ) hp hq
    (mapJoinCone U (nerveCone c))
    (mapJoinCone U (nerveCone ((Cone.postcompose η).obj (c.whisker δ))))
    (nerveConeWhiskerPostcomposeHom δ c η U)
  rw [nerveConeWhiskerPostcomposeHom_boundary]
  exact hη

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
