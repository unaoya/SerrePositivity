module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCompositionInputs
public import SerrePositivity.InfinityCategories.Derived.Gluing.ProductHomotopyEquivalence
/-!
概要：元入力付き二合成対応の対角と、元二作用の全区間 Hom を一致させる。
方針：実三角形の対角面を回収し、元切断の積を同じ二端点へ照合する。
規約：左右の元入力を保つ。使われ方：元終域の入力付き path 模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q

def dgGluingHomTargetFirstInputDiagonal :
    dgGluingHomTargetFirstInputFiber R C D E p q X Y ⟶
      intervalMappingSpace (X := dgNerve R E)
        (Simplex.vertex (p.obj X.left)) (Simplex.vertex (q.obj Y.right)) :=
  pullback.fst
    (dgGluingFirstFixedCompositionSecond (X := dgNerve R E)
      (Edge.ofTruncated (X := dgNerve R E)
        (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
      (Simplex.vertex (q.obj Y.right)))
    (dgGluingHomTargetRightIntervalInput R C D E p q X Y) ≫
  dgGluingFirstFixedCompositionDiagonal
    (Edge.ofTruncated (X := dgNerve R E)
      (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q X)))
    (Simplex.vertex (q.obj Y.right))

def dgGluingHomTargetLastInputDiagonal :
    dgGluingHomTargetLastInputFiber R C D E p q X Y ⟶
      intervalMappingSpace (X := dgNerve R E)
        (Simplex.vertex (p.obj X.left)) (Simplex.vertex (q.obj Y.right)) :=
  pullback.fst
    (compositionCorrespondenceFirst (X := dgNerve R E) (Simplex.vertex (p.obj X.left))
      (Edge.ofTruncated (X := dgNerve R E)
        (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y))))
    (dgGluingHomTargetLeftIntervalInput R C D E p q X Y) ≫
  compositionCorrespondenceDiagonal (X := dgNerve R E) (Simplex.vertex (p.obj X.left))
    (Edge.ofTruncated (X := dgNerve R E)
      (dgClosedEdge R E (dgHomGluingTargetMap R C D E p q Y)))

attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetFirstInputSection_diagonal :
    dgGluingHomTargetFirstInputSection R C D E p q X Y ≫
      dgGluingHomTargetFirstInputDiagonal R C D E p q X Y =
    complexPinchedMap.{u, max (u + 1) v} (dgGluingRightAction R C D M X Y) ≫
      (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom ≫
        pinchedHomToIntervalMappingSpace _ _ := by
  apply intervalMappingUncurry_injective _ _
  erw [dgGluingHomTargetFirstInputDiagonal, ← Category.assoc,
    dgGluingHomTargetFirstInputSection_composition]
  exact (dgGluingFirstFixedCompositionLift_diagonal _ _ _ _ _ _).trans
    (dgGluingHomTargetRightCompositionTriangle_diagonal R C D E p q X Y)

lemma dgGluingHomTargetLastInputSection_diagonal :
    dgGluingHomTargetLastInputSection R C D E p q X Y ≫
      dgGluingHomTargetLastInputDiagonal R C D E p q X Y =
    complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftAction R C D M X Y) ≫
      (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom ≫
        pinchedHomToIntervalMappingSpace _ _ := by
  apply intervalMappingUncurry_injective _ _
  erw [dgGluingHomTargetLastInputDiagonal, ← Category.assoc,
    dgGluingHomTargetLastInputSection_composition]
  exact (dgGluingLastFixedCompositionLift_diagonal _ _ _ _ _ _).trans
    (dgGluingHomTargetLeftCompositionTriangle_diagonal R C D E p q X Y)

def dgGluingHomTargetInputPairSection :=
  dgGluingHomTargetLastInputSection R C D E p q X Y ⊗ₘ
    dgGluingHomTargetFirstInputSection R C D E p q X Y

lemma dgGluingHomTargetInputPairSection_equivalence :
    IsSimplicialHomotopyEquivalence (dgGluingHomTargetInputPairSection R C D E p q X Y) :=
  dgGluingProductMap_homotopyEquivalence
    (dgGluingHomTargetLastInputSection_equivalence R C D E p q X Y)
    (dgGluingHomTargetFirstInputSection_equivalence R C D E p q X Y)

lemma dgGluingHomTargetInputPairSection_diagonals :
    dgGluingHomTargetCoefficientInputPair R C D E p q X Y ≫
      (pinchedHomToIntervalMappingSpace _ _ ⊗ₘ pinchedHomToIntervalMappingSpace _ _) =
    dgGluingHomTargetInputPairSection R C D E p q X Y ≫
      (dgGluingHomTargetLastInputDiagonal R C D E p q X Y ⊗ₘ
        dgGluingHomTargetFirstInputDiagonal R C D E p q X Y) := by
  let a := complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftAction R C D M X Y)
  let b := complexPinchedMap.{u, max (u + 1) v} (dgGluingRightAction R C D M X Y)
  let e := (dgGluingHomTargetCoefficientMappingIso R C D E p q X Y).hom
  let t := pinchedHomToIntervalMappingSpace (X := dgNerve R E)
    (Simplex.vertex (p.obj X.left)) (Simplex.vertex (q.obj Y.right))
  have hl : ((a ⊗ₘ b) ≫ (e ⊗ₘ e)) ≫ (t ⊗ₘ t) =
      (a ≫ e ≫ t) ⊗ₘ (b ≫ e ≫ t) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => (a ⊗ₘ b) ≫ k) (tensorHom_comp_tensorHom e e t t)).trans
        (tensorHom_comp_tensorHom a b (e ≫ t) (e ≫ t)))
  have hr := (tensorHom_comp_tensorHom
    (dgGluingHomTargetLastInputSection R C D E p q X Y)
    (dgGluingHomTargetFirstInputSection R C D E p q X Y)
    (dgGluingHomTargetLastInputDiagonal R C D E p q X Y)
    (dgGluingHomTargetFirstInputDiagonal R C D E p q X Y)).trans
      (congrArg₂ (fun l r => l ⊗ₘ r)
        (dgGluingHomTargetLastInputSection_diagonal R C D E p q X Y)
        (dgGluingHomTargetFirstInputSection_diagonal R C D E p q X Y))
  exact hl.trans hr.symm

end SerrePositivity.InfinityCategories
