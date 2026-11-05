module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitTriangleFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.UnitCapPastingCoefficientFace
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCanonicalFace
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitTriangleDiagrams
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetDiagonalRelativeNormalization
public import SerrePositivity.InfinityCategories.Derived.Gluing.RelativePrismEdgeClass
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitCapIntervalTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetUnitCollarIntervalTriangle
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "IX" => dgGluingHomTargetIdentityCommaObject R C D E p q X
local notation "IY" => dgGluingHomTargetIdentityCommaObject R C D E p q Y
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetPostAugmentationTriangle_normalized :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
      dgGluingHomTargetPostAugmentationTriangle R C D E p q X Y =
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 P)) ≫
      dgGluingHomTargetPostNormalizeCube R C D E p q X Y := by
  rw [dgGluingHomTargetPostAugmentationTriangle, ← Category.assoc,
    dgGluingAugmentationTriangle_cube_post_normalized.{u, max (u + 1) v}
      R E IX IY (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)]
  rfl

lemma dgGluingHomTargetAugmentationTetrahedron_normalized_edge :
    (Δ[1] ◁ ((stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (1 : Fin 4)) ▷ P)) ≫
      dgGluingHomTargetAugmentationTetrahedron R C D E p q X Y =
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0 P)) ≫
      dgGluingHomTargetPostNormalizeCube R C D E p q X Y := by
  rw [comp_whiskerRight, whiskerLeft_comp, Category.assoc,
    dgGluingHomTargetAugmentationTetrahedron_one R C D E p q X Y,
    dgGluingHomTargetPostAugmentationTriangle_normalized R C D E p q X Y]

lemma dgGluingHomTargetUnitCapPastingTriangleFamily_coefficient_diagonal :
    (Δ[1] ◁ (stdSimplex.δ (1 : Fin 3) ▷ P)) ≫
      dgGluingHomTargetUnitCapPastingTriangleFamily R C D E p q X Y 4 =
    (Δ[1] ◁ dgGluingHomTargetNormalizedPrism R C D E p q X Y) ≫
      dgGluingHomTargetCoefficientIntervalEvaluation R E C D p q X Y := by
  rw [dgGluingHomTargetUnitCapPastingTriangleFamily, ← Category.assoc,
    dgGluingUnitCapPastingDomain_coefficient_diagonal]
  simp only [Category.assoc]
  rw [dgGluingHomTargetAugmentationTetrahedron_normalized_edge R C D E p q X Y,
    dgGluingHomTargetPostNormalizeCube_canonical_face R E C D p q X Y,
    dgGluingPrismIntervalSquare_swap]

lemma dgGluingHomTargetUnitCapIntervalTriangle_coefficient_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ P) ≫
      dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y 4 =
    dgGluingHomTargetNormalizedIntervalPrism R C D E p q X Y := by
  apply intervalMappingUncurry_injective _ _
  rw [intervalMappingUncurry_precomp,
    dgGluingHomTargetUnitCapIntervalTriangle_evaluate,
    dgGluingHomTargetUnitCapPastingTriangleFamily_coefficient_diagonal]
  rw [dgGluingHomTargetNormalizedIntervalPrism, intervalMappingUncurry_precomp]
  rfl

def dgGluingHomTargetAugmentationDiagonalHomotopy :=
  dgGluingHomotopyOfRelativePrism (dgGluingHomTargetCoefficientDiagonalHomotopy R C D E p q X Y)
    (Classical.choose (dgGluingHomTargetDiagonalRelativeNormalization_exists R C D E p q X Y))
    (Classical.choose_spec
      (dgGluingHomTargetDiagonalRelativeNormalization_exists R C D E p q X Y))

lemma dgGluingHomTargetAugmentationDiagonalHomotopy_class :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgGluingHomTargetAugmentationDiagonalHomotopy R C D E p q X Y)) =
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
      (dgGluingHomTargetCoefficientDiagonalHomotopy R C D E p q X Y)) :=
  dgGluingHomotopyOfRelativePrism_homMk_eq _ _ _

lemma dgGluingHomTargetUnitCapTriangleDiagram_coefficient_homotopy :
    stdSimplex.δ (1 : Fin 3) ≫
      dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 4 =
    curry (dgGluingHomTargetAugmentationDiagonalHomotopy R C D E p q X Y).h := by
  rw [dgGluingHomTargetUnitCapTriangleDiagram, dgGluingTriangleDiagramTransport_face,
    dgGluingHomTargetUnitCapIntervalTriangle_coefficient_diagonal]
  apply congrArg curry
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

end SerrePositivity.InfinityCategories
