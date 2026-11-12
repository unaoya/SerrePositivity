module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostHomCriterion
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalDiagramRestrictionFibration
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.StrictKanPullbackMapEquivalence
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial
variable {X Y K : SSet.{u}} (p : X ⟶ Y) (x y : X _⦋0⦌)
  (a : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (p.app _ x) (p.app _ y))

lemma dgGluingPinchedIntervalPost_naturality :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (p.app _ x) (p.app _ y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq p x y rfl rfl := by
  simpa only [eqToHom_refl, Category.comp_id] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_postOfEq p x y rfl rfl

def dgGluingPinchedIntervalPullbackTransport :
    pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y) a ⟶
      pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq p x y rfl rfl)
        (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (p.app _ x) (p.app _ y)) :=
  pullback.map _ _ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y) (𝟙 K)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (p.app _ x) (p.app _ y))
    (dgGluingPinchedIntervalPost_naturality p x y) (by rw [Category.id_comp])

lemma dgGluingPinchedIntervalPullbackTransport_equivalence
    [Quasicategory X] [Quasicategory Y] [KanComplex K]
    [Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y)] (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (dgGluingPinchedIntervalPullbackTransport p x y a) := by
  let : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq p x y rfl rfl) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_fibration p hp x y rfl rfl
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.strictKanPullbackMap_homotopyEquivalence _ _ _ _ _ _ _
    (dgGluingPinchedIntervalPost_naturality p x y) (by rw [Category.id_comp])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence x y).isSimplicialHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isSimplicialHomotopyEquivalence_id _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence (p.app _ x) (p.app _ y)).isSimplicialHomotopyEquivalence
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
