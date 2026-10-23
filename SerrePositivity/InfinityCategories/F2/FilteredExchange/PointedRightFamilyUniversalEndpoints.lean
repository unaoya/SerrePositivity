module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedRightFamilyTransport

/-!
概要：全直積上の右 Hom 比較の二作用を、任意の実係数で厳密に評価する。
方針：同じ直積の二射影と対角輸送の前合成公式を使う。
規約：元の動く点・射を保つ。使われ方：同じ全右 Hom 比較の自然性正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {K L : KanObject.{u}} {P : SSet.{u + 1}}
  (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj)
  (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))
local notation "A" => CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj K)
local notation "H" => CategoryTheory.Functor.obj SSet.uliftFunctor (SimplicialCategory.sHom K L)

/-- 全直積上の評価と元の右 fiber 比較の作用は、元の動く点と射の評価そのもの。 -/
lemma pointedRightFamilyUniversal_source :
    lift x y ≫ pointedRightFamilyEvaluation (fst A H) (snd A H) ≫
        pointedRightFiberComparison L =
      pointedRightFamilyEvaluation x y ≫ pointedRightFiberComparison L := by
  rfl

/-- 全直積上の同じ輸送作用は、元の同じ動く点・射の対角輸送そのもの。 -/
lemma pointedRightFamilyUniversal_target :
    lift x y ≫ diagonalFiberTransport pointedSpaceProjection
        (fst A H ≫ pointedRightFiberComparison K) (snd A H ≫ coherentKanRightHomInterval K L) =
      diagonalFiberTransport pointedSpaceProjection (x ≫ pointedRightFiberComparison K)
        (y ≫ coherentKanRightHomInterval K L) := by
  rw [diagonalFiberTransport_precomp]
  simp only [← Category.assoc, lift_fst, lift_snd]

end SerrePositivity.InfinityCategories.F2
