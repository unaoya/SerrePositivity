module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGOrderedFunctorDiagram
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGStrictFunctorCategory
/-!
概要：通常の厳密 dg 関手図式と元の二変換の合成から、指定相図式を構成する。
方針：同じ厳密変換と全斉次射の相間輸送、実関手の恒等・合成則を使う。
規約：関手圏の変換の等式は実単体で証明する。使われ方：kernel 比較の合成 coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {C : Type v} {E : Type w}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
/-- 厳密 dg 関手の通常の関手図式から、同じ順序相の図式を得る。 -/
def dgOrderedFunctorDiagramOfFunctor {I : Type t} [Preorder I]
    (d : I ⥤ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOrderedFunctorDiagram R C E I where
  obj p := (d.obj p).toDGFunctor
  map _p _q h := d.map (homOfLE h)
  map_refl p := d.map_id p
  map_trans _p _q _r hpq hqr := (d.map_comp (homOfLE hpq) (homOfLE hqr)).symm
/-- 元の二つの厳密 dg 自然変換とその同じ合成を持つ、三相の実図式。 -/
def dgStrictNatTransCompositionDiagram {F G H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G H) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOrderedFunctorDiagram R C E (Fin 3) := by
  let a : (⟨F⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E) ⟶ ⟨G⟩ := η
  let b : (⟨G⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E) ⟶ ⟨H⟩ := θ
  exact dgOrderedFunctorDiagramOfFunctor (ComposableArrows.mk₂ a b)
/-- 元の三相図式の第零関手は元の F。 -/
lemma dgStrictNatTransCompositionDiagram_obj_zero {F G H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G H) :
    (dgStrictNatTransCompositionDiagram η θ).obj 0 = F := rfl
/-- 元の三相図式の第一関手は元の G。 -/
lemma dgStrictNatTransCompositionDiagram_obj_one {F G H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G H) :
    (dgStrictNatTransCompositionDiagram η θ).obj 1 = G := rfl
/-- 元の三相図式の第二関手は元の H。 -/
lemma dgStrictNatTransCompositionDiagram_obj_two {F G H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G H) :
    (dgStrictNatTransCompositionDiagram η θ).obj 2 = H := rfl
/-- 元の三相図式の零から一への変換は元の第一変換。 -/
lemma dgStrictNatTransCompositionDiagram_map_zero_one {F G H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G H) :
    (dgStrictNatTransCompositionDiagram η θ).map 0 1 (by decide) = η := rfl
/-- 元の三相図式の一から二への変換は元の第二変換。 -/
lemma dgStrictNatTransCompositionDiagram_map_one_two {F G H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G H) :
    (dgStrictNatTransCompositionDiagram η θ).map 1 2 (by decide) = θ := rfl
/-- 元の三相図式の零から二への変換は元の同じ通常順合成。 -/
lemma dgStrictNatTransCompositionDiagram_map_zero_two {F G H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G H) :
    (dgStrictNatTransCompositionDiagram η θ).map 0 2 (by decide) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp η θ := rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
