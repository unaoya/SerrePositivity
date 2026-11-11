module

public import Mathlib.CategoryTheory.Presentable.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
概要：射の総数が μ 未満の通常の極限は、μ-filtered な通常の余極限を保つ。
方針：極限関手を評価関手の点ごとの極限として表し、集合の正則濃度版の交換を使う。
規約：ここでは Type の strict な図式を扱う。coherent な Space の交換は別途必要。
使われ方：μ-small な weighted 極限の、次数ごとの交換。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 通常の極限関手を、元の各対象での評価関手の極限として表す余錐。 -/
def limitEvaluationCone (K : Type u) [SmallCategory K] :
    Cone (evaluation K (Type u)) where
  pt := lim
  π :=
    { app k :=
        { app X := limit.π X k
          naturality := by intros; simp }
      naturality := by intros; ext X; simp }

/-- 評価関手の同じ余錐は、関手圏の極限余錐。 -/
def limitEvaluationCone_isLimit (K : Type u) [SmallCategory K] :
    IsLimit (limitEvaluationCone K) :=
  evaluationJointlyReflectsLimits _ (fun X ↦ limit.isLimit X)

/-- 射の総数が μ 未満の極限関手は、μ-filtered な通常の余極限を保つ。 -/
lemma smallLimit_isCardinalAccessible {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (K : Type u) [SmallCategory K] (hK : HasCardinalLT (Arrow K) μ) :
    (lim : (K ⥤ Type u) ⥤ Type u).IsCardinalAccessible μ := by
  have (k : K) : ((evaluation K (Type u)).obj k).IsCardinalAccessible μ := ⟨fun _ _ _ ↦ by
    infer_instance⟩
  exact Functor.isCardinalAccessible_of_isLimit (limitEvaluationCone K)
    (limitEvaluationCone_isLimit K) μ hK

/-- 任意の指定された μ-filtered 余極限に対する、同じ通常の極限関手の保存性。 -/
lemma smallLimit_preservesCardinalFilteredColimits {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (K : Type u) [SmallCategory K] (hK : HasCardinalLT (Arrow K) μ)
    (I : Type u) [SmallCategory I] [IsCardinalFiltered I μ] :
    PreservesColimitsOfShape I (lim : (K ⥤ Type u) ⥤ Type u) := by
  have := smallLimit_isCardinalAccessible K hK
  exact Functor.preservesColimitsOfShape_of_isCardinalAccessible _ μ I

/-- 同じ小さい極限の交換を、全次数を通じた通常の単体集合図式へ移す。 -/
lemma smallSSetLimit_preservesCardinalFilteredColimits {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (K : Type u) [SmallCategory K] (hK : HasCardinalLT (Arrow K) μ)
    (I : Type u) [SmallCategory I] [IsCardinalFiltered I μ] :
    PreservesColimitsOfShape I (lim : (K ⥤ SSet.{u}) ⥤ SSet.{u}) := by
  have := smallLimit_preservesCardinalFilteredColimits K hK I
  apply preservesColimitsOfShape_of_evaluation
  intro n
  have : PreservesColimitsOfShape I
      ((Functor.whiskeringRight K SSet.{u} (Type u)).obj ((evaluation _ _).obj n) ⋙ lim) :=
    inferInstance
  exact preservesColimitsOfShape_of_natIso (preservesLimitNatIso ((evaluation _ _).obj n)).symm

/-- 元の strict な単体集合図式に対する、小さい極限と μ-filtered 余極限の比較同型。 -/
def smallSSetLimitColimitIso {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (K : Type u) [SmallCategory K] (hK : HasCardinalLT (Arrow K) μ)
    (I : Type u) [SmallCategory I] [IsCardinalFiltered I μ] (F : I ⥤ K ⥤ SSet.{u}) :
    colimit (F ⋙ lim) ≅ limit (colimit F) := by
  have := smallSSetLimit_preservesCardinalFilteredColimits K hK I
  exact (preservesColimitIso (lim : (K ⥤ SSet.{u}) ⥤ SSet.{u}) F).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
