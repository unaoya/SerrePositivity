module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StrictIntervalMappingLift
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：一次元の図式の間の全 strict 変換空間は、同じ成分評価による pullback。
方針：元の自然性の等式と、全パラメーターでの成分の復元・一意性を使う。
規約：二つの図式の値の充填性を仮定しない。
使われ方：一次元セルの元の Hom と coherent な Hom の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 一次元の元の strict 変換空間の二成分評価は、元の後合成・前合成の pullback。 -/
lemma strictIntervalMapping_isPullback (F G : ULift.{u} (Fin 2) ⥤ SSet.{u}) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G (ULift.up 0))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G (ULift.up 1))
      ((ihom (F.obj (ULift.up 0))).map (G.map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictIntervalIndexArrow))
      ((pre (F.map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictIntervalIndexArrow)).app (G.obj (ULift.up 1))) := by
  refine IsPullback.mk' (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictDiagramMappingComponent_naturality F G _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictIntervalIndexArrow)
    ?_ ?_
  · intro T m n h₀ h₁
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.strictIntervalMapping_hom_ext F G m n h₀ h₁
  · intro T a b h
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.strictIntervalMappingLift F G a b h,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.strictIntervalMappingLift_zero F G a b h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.strictIntervalMappingLift_one F G a b h⟩

/-- 同じ一次元の全変換空間を、元の二成分の標準 pullback で厳密に表示する。 -/
def strictIntervalMappingPullbackIso (F G : ULift.{u} (Fin 2) ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F G ≅
      pullback ((ihom (F.obj (ULift.up 0))).map (G.map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictIntervalIndexArrow))
        ((pre (F.map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictIntervalIndexArrow)).app (G.obj (ULift.up 1))) :=
  (strictIntervalMapping_isPullback F G).isoPullback

/-- 同じ pullback 表示の第一射影は、元の零成分の評価。 -/
lemma strictIntervalMappingPullbackIso_fst (F G : ULift.{u} (Fin 2) ⥤ SSet.{u}) :
    (strictIntervalMappingPullbackIso F G).hom ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G (ULift.up 0) :=
  (strictIntervalMapping_isPullback F G).isoPullback_hom_fst

/-- 同じ pullback 表示の第二射影は、元の一成分の評価。 -/
lemma strictIntervalMappingPullbackIso_snd (F G : ULift.{u} (Fin 2) ⥤ SSet.{u}) :
    (strictIntervalMappingPullbackIso F G).hom ≫ pullback.snd _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent F G (ULift.up 1) :=
  (strictIntervalMapping_isPullback F G).isoPullback_hom_snd

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
