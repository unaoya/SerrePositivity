module
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostHomCriterion
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalDiagramRestrictionFibration
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.StrictKanPullbackMapEquivalence
/-!
概要：pinched Hom の厳密引き戻しを同じ入力の区間 Hom の引き戻しへ移す。
方針：実後合成の自然性と二つの Kan fibration に沿う厳密引き戻し比較を用いる。
規約：追加のモデル圏構造を仮定せず、第二入力と元の二端点を保持する。
使われ方：正本 lax Hom 比較の標的を全区間の四座標模型へ輸送する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
variable {X Y K : SSet.{u}} (p : X ⟶ Y) (x y : X _⦋0⦌)
  (a : K ⟶ pinchedHom (p.app _ x) (p.app _ y))

lemma dgGluingPinchedIntervalPost_naturality :
    pinchedHomMap p x y ≫ pinchedHomToIntervalMappingSpace (p.app _ x) (p.app _ y) =
      pinchedHomToIntervalMappingSpace x y ≫ intervalMappingPostOfEq p x y rfl rfl := by
  simpa only [eqToHom_refl, Category.comp_id] using
    pinchedHomToIntervalMappingSpace_postOfEq p x y rfl rfl

def dgGluingPinchedIntervalPullbackTransport :
    pullback (pinchedHomMap p x y) a ⟶
      pullback (intervalMappingPostOfEq p x y rfl rfl)
        (a ≫ pinchedHomToIntervalMappingSpace (p.app _ x) (p.app _ y)) :=
  pullback.map _ _ _ _ (pinchedHomToIntervalMappingSpace x y) (𝟙 K)
    (pinchedHomToIntervalMappingSpace (p.app _ x) (p.app _ y))
    (dgGluingPinchedIntervalPost_naturality p x y) (by rw [Category.id_comp])

lemma dgGluingPinchedIntervalPullbackTransport_equivalence
    [Quasicategory X] [Quasicategory Y] [KanComplex K]
    [Fibration (pinchedHomMap p x y)] (hp : F1B.EquivalenceLifting p) :
    IsSimplicialHomotopyEquivalence (dgGluingPinchedIntervalPullbackTransport p x y a) := by
  let : Fibration (intervalMappingPostOfEq p x y rfl rfl) :=
    intervalMappingPostOfEq_fibration p hp x y rfl rfl
  exact F2.strictKanPullbackMap_homotopyEquivalence _ _ _ _ _ _ _
    (dgGluingPinchedIntervalPost_naturality p x y) (by rw [Category.id_comp])
    (pinchedHomToIntervalMappingSpace_isQCatEquivalence x y).isSimplicialHomotopyEquivalence
    (isSimplicialHomotopyEquivalence_id _)
    (pinchedHomToIntervalMappingSpace_isQCatEquivalence (p.app _ x) (p.app _ y)).isSimplicialHomotopyEquivalence
end SerrePositivity.InfinityCategories
