module

public import SerrePositivity.InfinityCategories.F1.CoherentCompositionSquare
public import SerrePositivity.InfinityCategories.F1.TransportIntervalSquare

/-!
概要：元の右 Hom の合成四角形を、同じ四辺を保つ区間輸送の図式にする。
方針：第一射・第二射・合成射の標準区間比較と最終の定値辺をそのまま使う。
規約：二つの Hom の全パラメーターを保ち、反転や逆同値は使わない。
使われ方：実際の pointed-space 輸送の合成則を元の Kan 合成と照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の二つの右 Hom の全体を保つ、第一射・第二射・合成射・定値辺の輸送四角形。 -/
def coherentCompositionIntervalSquare {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y Z : C) :
    TransportIntervalSquare
      ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⊗
        (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z))
      (coherentNerveVertex X) (coherentNerveVertex Y) (coherentNerveVertex Z)
      (coherentNerveVertex Z) where
  bottom := fst _ _ ≫ coherentHomComparison X Y ≫ pinchedHomToIntervalMappingSpace _ _
  top := intervalMappingCurryOfEndpoints (SSet.const (coherentNerveVertex Z))
    (SSet.comp_const _ _) (SSet.comp_const _ _)
  left := coherentHomComposition X Y Z ≫ coherentHomComparison X Z ≫
    pinchedHomToIntervalMappingSpace _ _
  right := snd _ _ ≫ coherentHomComparison Y Z ≫ pinchedHomToIntervalMappingSpace _ _
  square := coherentCompositionSquare X Y Z
  zero := by
    exact (coherentCompositionSquare_zero X Y Z).trans
      (intervalMappingUncurry_precomp (fst _ _)
        (coherentHomComparison X Y ≫ pinchedHomToIntervalMappingSpace _ _)).symm
  one := by
    rw [coherentCompositionSquare_one, intervalMappingUncurry_curryOfEndpoints]
  inner_zero := coherentCompositionSquare_inner_zero X Y Z
  inner_one := coherentCompositionSquare_inner_one X Y Z

/-- 最終の区間族は、元の合成四角形の固定終点に厳密に定値。 -/
lemma coherentCompositionIntervalSquare_top {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y Z : C) :
    intervalMappingUncurry (coherentCompositionIntervalSquare X Y Z).top =
      SSet.const (coherentNerveVertex Z) := by
  dsimp only [coherentCompositionIntervalSquare]
  rw [intervalMappingUncurry_curryOfEndpoints]

end SerrePositivity.InfinityCategories
