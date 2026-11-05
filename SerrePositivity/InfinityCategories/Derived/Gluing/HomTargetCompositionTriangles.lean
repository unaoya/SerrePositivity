module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCoefficientActions
public import SerrePositivity.InfinityCategories.Derived.Gluing.DGCompositionTriangleFamily
public import SerrePositivity.InfinityCategories.Derived.Gluing.ClosedPostcompositionAW
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedConstantIntervalFamilies
/-!
概要：元二脚の左右 Hom 入力と実 augmentation の合成三角形を元終域に構成する。
方針：実 dg 合成 prism を使い、全三辺を同じ二作用へ照合する。
規約：標準三角形の全族を保持する。使われ方：元終域の入力付き合成対応。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q

def dgGluingHomTargetLeftIntervalInput :=
  dgGluingHomTargetLeftCoefficientInput R C D E p q X Y ≫
    pinchedHomToIntervalMappingSpace _ _

def dgGluingHomTargetRightIntervalInput :=
  dgGluingHomTargetRightCoefficientInput R C D E p q X Y ≫
    pinchedHomToIntervalMappingSpace _ _

def dgGluingHomTargetLeftCompositionTriangle :=
  dgGluingDGCompositionTriangleFamily R E
    (dgGluingHomTargetLeftCoefficientInput R C D E p q X Y)
    (SSet.const (pinchedClosedVertex R E (dgHomGluingTargetMap R C D E p q Y)))

def dgGluingHomTargetRightCompositionTriangle :=
  dgGluingDGCompositionTriangleFamily R E
    (SSet.const (pinchedClosedVertex R E (dgHomGluingTargetMap R C D E p q X)))
    (dgGluingHomTargetRightCoefficientInput R C D E p q X Y)

lemma dgGluingHomTargetLeftCompositionTriangle_variable :
    (stdSimplex.δ (2 : Fin 3) ▷ _) ≫
      dgGluingHomTargetLeftCompositionTriangle R C D E p q X Y =
    intervalMappingUncurry (dgGluingHomTargetLeftIntervalInput R C D E p q X Y) :=
  dgGluingDGCompositionTriangleFamily_two R E _ _

lemma dgGluingHomTargetRightCompositionTriangle_variable :
    (stdSimplex.δ (0 : Fin 3) ▷ _) ≫
      dgGluingHomTargetRightCompositionTriangle R C D E p q X Y =
    intervalMappingUncurry (dgGluingHomTargetRightIntervalInput R C D E p q X Y) :=
  dgGluingDGCompositionTriangleFamily_zero R E _ _

lemma dgGluingHomTargetLeftCompositionTriangle_fixed :
    (stdSimplex.δ (0 : Fin 3) ▷ _) ≫
      dgGluingHomTargetLeftCompositionTriangle R C D E p q X Y =
    CartesianMonoidalCategory.fst (Δ[1] : SSet.{max (u + 1) v})
      (complexPinchedSpace (homObject R C X.left Y.left)) ≫
        SSet.yonedaEquiv.symm (dgClosedEdge R E
          (dgHomGluingTargetMap R C D E p q Y)).edge := by
  rw [dgGluingHomTargetLeftCompositionTriangle, dgGluingDGCompositionTriangleFamily_zero,
    dgGluingPinchedConstantIntervalFamily]
  rfl

lemma dgGluingHomTargetRightCompositionTriangle_fixed :
    (stdSimplex.δ (2 : Fin 3) ▷ _) ≫
      dgGluingHomTargetRightCompositionTriangle R C D E p q X Y =
    CartesianMonoidalCategory.fst (Δ[1] : SSet.{max (u + 1) v})
      (complexPinchedSpace (homObject R D X.right Y.right)) ≫
        SSet.yonedaEquiv.symm (dgClosedEdge R E
          (dgHomGluingTargetMap R C D E p q X)).edge := by
  rw [dgGluingHomTargetRightCompositionTriangle, dgGluingDGCompositionTriangleFamily_two,
    dgGluingPinchedConstantIntervalFamily]
  rfl

lemma dgGluingHomTargetLeftCompositionTriangle_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ _) ≫
      dgGluingHomTargetLeftCompositionTriangle R C D E p q X Y =
    intervalMappingUncurry
      (complexPinchedMap (dgGluingLeftAction R C D M X Y) ≫
        (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom ≫
          pinchedHomToIntervalMappingSpace _ _) := by
  rw [dgGluingHomTargetLeftCompositionTriangle, dgGluingDGCompositionTriangleFamily_one,
    dgGluingPinchedCompositionFamily_closed_post,
    ← dgGluingHomTargetLeftCoefficientAction, Category.assoc]

lemma dgGluingHomTargetRightCompositionTriangle_diagonal :
    (stdSimplex.δ (1 : Fin 3) ▷ _) ≫
      dgGluingHomTargetRightCompositionTriangle R C D E p q X Y =
    intervalMappingUncurry
      (complexPinchedMap (dgGluingRightAction R C D M X Y) ≫
        (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom ≫
          pinchedHomToIntervalMappingSpace _ _) := by
  rw [dgGluingHomTargetRightCompositionTriangle, dgGluingDGCompositionTriangleFamily_one,
    dgGluingPinchedCompositionFamily_closed_pre,
    ← dgGluingHomTargetRightCoefficientAction, Category.assoc]

end SerrePositivity.InfinityCategories
