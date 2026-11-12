module

public import SerrePositivity.KST.Spectra.D3GradedTransformationAlgebra
public import SerrePositivity.KST.Spectra.EnrichedTransformationTriangleStages

/-!
概要：厳密豊穣変換の縦合成を、coherent nerve の同じ関手空間の合成へ移す。
方針：既存の三段円柱で三角形を実現し、三辺を元の指定区間族として回収する。
規約：成分の等式だけから関手同型の等式を推論しない。
使われ方：共通右射影の厳密構造正方形を、実関手同型の正方形へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D]
  {F G H : EnrichedFunctor SSet.{u} C D}
  (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
  (θ : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) G H)

/-- 指定二変換と同じ厳密縦合成を三辺とする、元の三段豊穣円柱の関手。 -/
def d3GradedCompositionTriangleEnriched :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object (Fin 3) C) D :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.functor F G H η θ (d3GradedComp η θ) (fun _ ↦ rfl)

/-- 同じ合成三角形の、全対象・全高次単体を持つ実族。 -/
def d3GradedCompositionTriangleFamily :
    SimplicialNerve C ⊗ (Δ[2] : SSet.{max u v}) ⟶ SimplicialNerve D :=
  EnrichedOrderedCylinder.nerveSimplexFamily 2 ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3GradedCompositionTriangleEnriched η θ)

lemma d3GradedCompositionTriangleEnriched_first :
    (EnrichedOrderedCylinder.reindex (C := C) (SimplexCategory.δ (2 : Fin 3)).toOrderHom).comp
      SSet (d3GradedCompositionTriangleEnriched η θ) =
        StrictEnrichedTransformation.cylinder F G η := by
  apply EnrichedFunctor.ext SSet
    (fun X ↦ by rcases X with ⟨j, x⟩; fin_cases j <;> rfl)
  rintro ⟨j, x⟩ ⟨k, y⟩
  fin_cases j <;> fin_cases k
  all_goals
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨p, f⟩
    solve
    | rfl
    | have hp := p.down.down
      norm_num [Fin.le_def] at hp

lemma d3GradedCompositionTriangleEnriched_second :
    (EnrichedOrderedCylinder.reindex (C := C) (SimplexCategory.δ (0 : Fin 3)).toOrderHom).comp
      SSet (d3GradedCompositionTriangleEnriched η θ) =
        StrictEnrichedTransformation.cylinder G H θ := by
  apply EnrichedFunctor.ext SSet
    (fun X ↦ by rcases X with ⟨j, x⟩; fin_cases j <;> rfl)
  rintro ⟨j, x⟩ ⟨k, y⟩
  fin_cases j <;> fin_cases k
  all_goals
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨p, f⟩
    solve
    | rfl
    | have hp := p.down.down
      norm_num [Fin.le_def] at hp

lemma d3GradedCompositionTriangleFamily_first :
    (𝟙 (SimplicialNerve C) ⊗ₘ stdSimplex.δ (2 : Fin 3)) ≫
      d3GradedCompositionTriangleFamily η θ = StrictEnrichedTransformation.family F G η := by
  have hn := EnrichedOrderedCylinder.nerveSimplexFamily_naturality
    (C := C) (SimplexCategory.δ (2 : Fin 3))
  change (𝟙 (SimplicialNerve C) ⊗ₘ stdSimplex.δ (2 : Fin 3)) ≫
    EnrichedOrderedCylinder.nerveSimplexFamily 2 = _ at hn
  rw [d3GradedCompositionTriangleFamily, ← Category.assoc,
    hn, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, d3GradedCompositionTriangleEnriched_first]
  rfl

lemma d3GradedCompositionTriangleFamily_second :
    (𝟙 (SimplicialNerve C) ⊗ₘ stdSimplex.δ (0 : Fin 3)) ≫
      d3GradedCompositionTriangleFamily η θ = StrictEnrichedTransformation.family G H θ := by
  have hn := EnrichedOrderedCylinder.nerveSimplexFamily_naturality
    (C := C) (SimplexCategory.δ (0 : Fin 3))
  change (𝟙 (SimplicialNerve C) ⊗ₘ stdSimplex.δ (0 : Fin 3)) ≫
    EnrichedOrderedCylinder.nerveSimplexFamily 2 = _ at hn
  rw [d3GradedCompositionTriangleFamily, ← Category.assoc,
    hn, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, d3GradedCompositionTriangleEnriched_second]
  rfl

lemma d3GradedCompositionTriangleFamily_outer :
    (𝟙 (SimplicialNerve C) ⊗ₘ stdSimplex.δ (1 : Fin 3)) ≫
      d3GradedCompositionTriangleFamily η θ =
        StrictEnrichedTransformation.family F H (d3GradedComp η θ) := by
  have hn := EnrichedOrderedCylinder.nerveSimplexFamily_naturality
    (C := C) (SimplexCategory.δ (1 : Fin 3))
  change (𝟙 (SimplicialNerve C) ⊗ₘ stdSimplex.δ (1 : Fin 3)) ≫
    EnrichedOrderedCylinder.nerveSimplexFamily 2 = _ at hn
  rw [d3GradedCompositionTriangleFamily, ← Category.assoc,
    hn, Category.assoc,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, d3GradedCompositionTriangleEnriched,
    EnrichedTransformationTriangle.functor_outer]
  rfl

/-- 同じ三辺を持つ関手空間内の実合成三角形。 -/
def d3GradedComposition_compStruct :
    SSet.Truncated.Edge.CompStruct
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (StrictEnrichedTransformation.homotopy F G η))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (StrictEnrichedTransformation.homotopy G H θ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (StrictEnrichedTransformation.homotopy F H (d3GradedComp η θ))) where
  simplex := SSet.yonedaEquiv (curry (d3GradedCompositionTriangleFamily η θ))
  d₂ := by
    change ((ihom (SimplicialNerve C)).obj (SimplicialNerve D)).δ 2 _ = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← curry_natural_left]
    rw [show (SimplicialNerve C) ◁ stdSimplex.δ (2 : Fin 3) =
      𝟙 (SimplicialNerve C) ⊗ₘ stdSimplex.δ (2 : Fin 3) from rfl,
      d3GradedCompositionTriangleFamily_first]
    rfl
  d₀ := by
    change ((ihom (SimplicialNerve C)).obj (SimplicialNerve D)).δ 0 _ = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← curry_natural_left]
    rw [show (SimplicialNerve C) ◁ stdSimplex.δ (0 : Fin 3) =
      𝟙 (SimplicialNerve C) ⊗ₘ stdSimplex.δ (0 : Fin 3) from rfl,
      d3GradedCompositionTriangleFamily_second]
    rfl
  d₁ := by
    change ((ihom (SimplicialNerve C)).obj (SimplicialNerve D)).δ 1 _ = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← curry_natural_left]
    rw [show (SimplicialNerve C) ◁ stdSimplex.δ (1 : Fin 3) =
      𝟙 (SimplicialNerve C) ⊗ₘ stdSimplex.δ (1 : Fin 3) from rfl,
      d3GradedCompositionTriangleFamily_outer]
    rfl

/-- 厳密変換の縦合成は、同じ指定関手辺のホモトピー圏の合成を回収する。 -/
lemma d3GradedComposition_hom_trans [Quasicategory (SimplicialNerve D)] :
    SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (StrictEnrichedTransformation.homotopy F G η)) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (StrictEnrichedTransformation.homotopy G H θ)) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (StrictEnrichedTransformation.homotopy F H (d3GradedComp η θ))) :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk (d3GradedComposition_compStruct η θ)

/-- 元の厳密変換の指定区間族を、同じ関手空間のホモトピー圏の射として保持する。 -/
def d3GradedHom [Quasicategory (SimplicialNerve D)]
    {F G : EnrichedFunctor SSet.{u} C D}
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G) :
    SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap F)) ⟶
      SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap G)) :=
  SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (StrictEnrichedTransformation.homotopy F G η))

/-- 元の厳密変換の実現は、関手空間の射の合成を保つ。 -/
lemma d3GradedHom_comp [Quasicategory (SimplicialNerve D)] :
    d3GradedHom η ≫ d3GradedHom θ = d3GradedHom (d3GradedComp η θ) :=
  d3GradedComposition_hom_trans η θ

/-- 厳密変換から構成済みの関手同型の順射は、この同じ指定辺の類。 -/
lemma d3GradedHom_functorIso [Quasicategory (SimplicialNerve D)]
    (hη : ∀ X, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (StrictEnrichedTransformation.componentHom F G η X)).toTruncated) :
    (StrictEnrichedTransformation.functorIso F G η hη).hom = d3GradedHom η := rfl

end SerrePositivity.KST.Spectra
