module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetArrowComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetOriginalPrism
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowHomActionPrism
/-!
概要：元矢印 Hom の全正方形は、前正規化 cube の元面と同じである。
方針：関手値 Hom の全 prism 自然性を元 augmentation 全族へ適用する。
規約：元二三角形と共通対角を同時に保持する。
使われ方：単位補正道の元端を指定 lax 比較の二三角形へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q

abbrev dgGluingHomTargetHomParameter : SSet.{max (u + 1) v} :=
  complexPinchedSpace.{u, max (u + 1) v} (dgGluingHomComplex R C D M X Y)
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y

attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetNormalization_original_square :
    (Δ[1] ◁ intervalMappingUncurry
      (dgGluingHomTargetNormalizationHomInput R C D E p q X Y ≫
        pinchedHomToIntervalMappingSpace _ _)) ≫
      dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) ≫
        dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E) =
    (Δ[1] ◁ dgGluingHomTargetHomIntervalEvaluation R C D E p q X Y) ≫
      (β_ (Δ[1] : SSet.{max (u + 1) v})
        (dgNerve R (DGGluingObject R C D M))).hom ≫
          (dgGluingHomTargetAugmentationHomotopy R C D E p q).h := by
  have h := dgGluingHomTargetPreNormalizeCube_original_face R C D E p q X Y
  rw [dgGluingHomTargetPreNormalizeCube, ← Category.assoc,
    dgGluingIdentityCommaPreNormalizeCube_interval_one] at h
  exact h

lemma dgGluingHomTargetArrowIntervalComparison_prism :
    intervalFunctorHomPrism (dgGluingHomTargetArrowIntervalComparison R C D E p q X Y) =
    ((β_ (Δ[1] : SSet.{max (u + 1) v}) Δ[1]).hom ▷ P) ≫
      (α_ Δ[1] Δ[1] P).hom ≫
        (Δ[1] ◁ dgGluingHomTargetHomIntervalEvaluation R C D E p q X Y) ≫
          (β_ (Δ[1] : SSet.{max (u + 1) v})
            (dgNerve R (DGGluingObject R C D M))).hom ≫
              (dgGluingHomTargetAugmentationHomotopy R C D E p q).h := by
  have h := dgGluingArrowHomActionPrism
    (dgGluingHomTargetAugmentationArrowFamily R C D E p q)
    (dgGluingHomTargetArrowDiagram_vertex R C D E p q X)
    (dgGluingHomTargetArrowDiagram_vertex R C D E p q Y)
    (dgGluingHomMappingIso R C D M X Y).inv
  simpa only [dgGluingHomTargetArrowIntervalComparison,
    dgGluingHomTargetAugmentationArrowFamily, dgGluingHomTargetHomIntervalEvaluation,
    uncurry_curry, Category.assoc] using h

def dgGluingHomTargetNormalizationArrowSquare :=
  ((β_ (Δ[1] : SSet.{max (u + 1) v}) Δ[1]).hom ▷ P) ≫
    (α_ Δ[1] Δ[1] P).hom ≫
      (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 1 P)) ≫
        dgGluingHomTargetPreNormalizeCube R C D E p q X Y

lemma dgGluingHomTargetArrowIntervalComparison_prism_cube :
    intervalFunctorHomPrism (dgGluingHomTargetArrowIntervalComparison R C D E p q X Y) =
      dgGluingHomTargetNormalizationArrowSquare R C D E p q X Y := by
  rw [dgGluingHomTargetNormalizationArrowSquare,
    dgGluingHomTargetPreNormalizeCube_original_face]
  exact dgGluingHomTargetArrowIntervalComparison_prism R C D E p q X Y

def dgGluingHomTargetArrowTriangles :=
  dgGluingArrowHomTrianglePairOfInterval
    (dgGluingHomTargetArrowDiagram R C D E p q X)
    (dgGluingHomTargetArrowDiagram R C D E p q Y)
    (dgGluingHomTargetArrowIntervalComparison R C D E p q X Y)

end SerrePositivity.InfinityCategories
