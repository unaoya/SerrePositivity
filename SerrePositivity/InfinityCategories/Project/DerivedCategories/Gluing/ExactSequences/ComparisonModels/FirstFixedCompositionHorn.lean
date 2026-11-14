module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ComposableHomHorn

/-! 指定した第一辺と、第二辺の全 Hom 空間の族を同じ内ホーンへ貼る。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {X : SSet.{u}} {x y : X _⦋0⦌} (f : X.Edge x y) (z : X _⦋0⦌)
local notation "H" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y z

def dgGluingFirstFixedCompositionHorn : (horn 2 1 : SSet.{u}) ⊗ H ⟶ X :=
  (horn₂₁.isPushout.map (tensorRight H)).desc
    (fst (Δ[1] : SSet.{u}) H ≫ SSet.yonedaEquiv.symm f.edge)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (𝟙 H)) (by
      change (stdSimplex.δ (0 : Fin 2) ▷ H) ≫ fst (Δ[1] : SSet.{u}) H ≫
          SSet.yonedaEquiv.symm f.edge =
        (stdSimplex.δ (1 : Fin 2) ▷ H) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (𝟙 H)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_face_source, ← Category.assoc, whiskerRight_fst,
        Category.assoc, f.δ_zero_yonedaEquiv_symm])

lemma dgGluingFirstFixedCompositionHorn_first :
    (horn₂₁.ι₀₁ ▷ H) ≫ dgGluingFirstFixedCompositionHorn f z =
      fst (Δ[1] : SSet.{u}) H ≫ SSet.yonedaEquiv.symm f.edge :=
  (horn₂₁.isPushout.map (tensorRight H)).inl_desc _ _ _

lemma dgGluingFirstFixedCompositionHorn_last :
    (horn₂₁.ι₁₂ ▷ H) ≫ dgGluingFirstFixedCompositionHorn f z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (𝟙 H) :=
  (horn₂₁.isPushout.map (tensorRight H)).inr_desc _ _ _

def dgGluingFirstFixedCompositionHornMap : H ⟶ (ihom (horn 2 1 : SSet.{u})).obj X :=
  curry (dgGluingFirstFixedCompositionHorn f z)

lemma dgGluingFirstFixedCompositionHornMap_first {T : SSet.{u}} (a : T ⟶ H) :
    (horn₂₁.ι₀₁ ▷ T) ≫ uncurry (a ≫ dgGluingFirstFixedCompositionHornMap f z) =
      fst (Δ[1] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm f.edge := by
  rw [uncurry_natural_left, dgGluingFirstFixedCompositionHornMap, uncurry_curry,
    ← Category.assoc, ← whisker_exchange, Category.assoc,
    dgGluingFirstFixedCompositionHorn_first, ← Category.assoc, whiskerLeft_fst]

lemma dgGluingFirstFixedCompositionHornMap_last {T : SSet.{u}} (a : T ⟶ H) :
    (horn₂₁.ι₁₂ ▷ T) ≫ uncurry (a ≫ dgGluingFirstFixedCompositionHornMap f z) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry a := by
  rw [uncurry_natural_left, dgGluingFirstFixedCompositionHornMap, uncurry_curry,
    ← Category.assoc, ← whisker_exchange, Category.assoc,
    dgGluingFirstFixedCompositionHorn_last, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    Category.comp_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
