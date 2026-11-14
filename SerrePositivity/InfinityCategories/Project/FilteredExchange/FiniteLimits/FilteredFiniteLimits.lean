module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：単体集合の通常の filtered 余極限は有限極限を保つ。
方針：各次数の集合の filtered 余極限の正確性を評価関手で束ねる。
規約：ここでの極限は通常の圏の極限。homotopy 極限への比較は別に行う。
使われ方：path 置換と homotopy pullback の filtered 連続性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：単体集合の filtered 余極限関手は通常の有限極限を保つ。
方針：評価と余極限の自然同型を通して集合の正確性を使う。
規約：添字は同じ宇宙の通常の小さい filtered 圏。使われ方：引き戻しの標準比較。 -/
instance filteredColimit_preservesFiniteLimits {I : Type u} [SmallCategory I] [IsFiltered I] :
    PreservesFiniteLimits (colim : (I ⥤ SSet.{u}) ⥤ SSet.{u}) where
  preservesFiniteLimits J _ _ := by
    apply preservesLimitsOfShape_of_evaluation
    intro d
    have : PreservesLimitsOfShape J
        ((Functor.whiskeringRight I SSet.{u} (Type u)).obj ((evaluation _ _).obj d) ⋙ colim) :=
      inferInstance
    exact preservesLimitsOfShape_of_natIso (preservesColimitNatIso ((evaluation _ _).obj d)).symm

variable {I : Type u} [SmallCategory I] [IsFiltered I] {F G H : I ⥤ SSet.{u}}

/-- 概要：通常の filtered 余極限と関手圏の引き戻しの標準比較同型。
方針：有限極限保存の標準同型を使う。
規約：各値の Kan 性は不要。使われ方：二段の path 引き戻しの交換。 -/
def filteredPullbackIso (η : F ⟶ G) (θ : H ⟶ G) :
    colimit (pullback η θ) ≅ pullback (colim.map η) (colim.map θ) :=
  PreservesPullback.iso colim η θ

/-- 概要：引き戻しの比較は第一射影を保つ。
方針：有限極限保存の射影の公式。
規約：実際の標準比較の式。使われ方：path 座標の比較。 -/
lemma filteredPullbackIso_fst (η : F ⟶ G) (θ : H ⟶ G) :
    (filteredPullbackIso η θ).hom ≫ pullback.fst _ _ = colim.map (pullback.fst η θ) :=
  PreservesPullback.iso_hom_fst colim η θ

/-- 概要：引き戻しの比較は第二射影を保つ。
方針：有限極限保存の射影の公式。
規約：実際の標準比較の式。使われ方：元の図式の座標の比較。 -/
lemma filteredPullbackIso_snd (η : F ⟶ G) (θ : H ⟶ G) :
    (filteredPullbackIso η θ).hom ≫ pullback.snd _ _ = colim.map (pullback.snd η θ) :=
  PreservesPullback.iso_hom_snd colim η θ

end SerrePositivity.InfinityCategories.Project.FilteredExchange
