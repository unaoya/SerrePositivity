module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitTriangleFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitCapPastingCoefficientFace
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetCanonicalFace
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitTriangleDiagrams
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetDiagonalRelativeNormalization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.RelativePrismEdgeClass
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitCapIntervalTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetUnitCollarIntervalTriangle
/-!
概要：六片の係数辺を元正規化 prism と同定し、指定係数道と両端固定で比較する。
方針：元の全入力・指定面・全区間族を保持する比較を合成する。
規約：追加の主経路仮定を置かない。使われ方：元 lax Hom 比較の逆の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "IX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaObject R C D E p q X
local notation "IY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetIdentityCommaObject R C D E p q Y
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetPostAugmentationTriangle_normalized :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPostAugmentationTriangle R C D E p q X Y =
    (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 P)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPostNormalizeCube R C D E p q X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPostAugmentationTriangle, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingAugmentationTriangle_cube_post_normalized.{u, max (u + 1) v}
      R E IX IY (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizationHomInput R C D E p q X Y)]
  rfl

lemma dgGluingHomTargetAugmentationTetrahedron_normalized_edge :
    (Δ[1] ◁ ((stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4)) ▷ P)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationTetrahedron R C D E p q X Y =
    (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 P)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPostNormalizeCube R C D E p q X Y := by
  rw [comp_whiskerRight, whiskerLeft_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationTetrahedron_one R C D E p q X Y,
    dgGluingHomTargetPostAugmentationTriangle_normalized R C D E p q X Y]

lemma dgGluingHomTargetUnitCapPastingTriangleFamily_coefficient_diagonal :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 4 =
    (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizedPrism R C D E p q X Y) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientIntervalEvaluation R E C D p q X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapPastingTriangleFamily, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitCapPastingDomain_coefficient_diagonal]
  simp only [Category.assoc]
  rw [dgGluingHomTargetAugmentationTetrahedron_normalized_edge R C D E p q X Y,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPostNormalizeCube_canonical_face R E C D p q X Y,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPrismIntervalSquare_swap]

lemma dgGluingHomTargetUnitCapIntervalTriangle_coefficient_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ P) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 4 =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizedIntervalPrism R C D E p q X Y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapIntervalTriangle_evaluate,
    dgGluingHomTargetUnitCapPastingTriangleFamily_coefficient_diagonal]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNormalizedIntervalPrism, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp]
  rfl

def dgGluingHomTargetAugmentationDiagonalHomotopy :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyOfRelativePrism (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientDiagonalHomotopy R C D E p q X Y)
    (Classical.choose (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetDiagonalRelativeNormalization_exists R C D E p q X Y))
    (Classical.choose_spec
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetDiagonalRelativeNormalization_exists R C D E p q X Y))

lemma dgGluingHomTargetAugmentationDiagonalHomotopy_class :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (dgGluingHomTargetAugmentationDiagonalHomotopy R C D E p q X Y)) =
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetCoefficientDiagonalHomotopy R C D E p q X Y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyOfRelativePrism_homMk_eq _ _ _

lemma dgGluingHomTargetUnitCapTriangleDiagram_coefficient_homotopy :
    stdSimplex.δ (1 : Fin 3) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 4 =
    curry (dgGluingHomTargetAugmentationDiagonalHomotopy R C D E p q X Y).h := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapTriangleDiagram, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleDiagramTransport_face,
    dgGluingHomTargetUnitCapIntervalTriangle_coefficient_diagonal]
  apply congrArg curry
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
