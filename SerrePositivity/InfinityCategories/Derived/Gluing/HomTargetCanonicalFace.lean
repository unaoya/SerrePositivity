module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetNormalizationCubes
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaPrismIntervalSquare
public import SerrePositivity.InfinityCategories.Derived.Gluing.PrismIntervalSquare
/-!
概要：元終域の後 cube の正規化面を、同じ実 pinched prism の全区間評価へ照合する。
方針：宇宙の上げ下げを相殺し、恒等 comma の全正方形比較へ元 Hom 入力を渡す。
規約：二つの時間と全入力を保つ。使われ方：元係数 path との相対比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type (max (u + 1) v)) [DGCategory R E]

lemma dgGluingIdentityCommaAugmentationPrism_down :
    dgGluingCommaAugmentationPrism R E E (DGFunctor.id E) ≫
      dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E) =
    dgGluingIdentityCommaAugmentationPrism R E := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨β, s⟩
  apply Simplex.ext
  change ((dgCommaAugmentationPrismSimplex R E E (DGFunctor.id E) s
    (stdSimplex.objEquiv β).toOrderHom).toSimplexData.map
    (dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R E)).map
    (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R E) = _
  rw [← SimplexData.map_comp, dgUniverseLiftUp_comp_down, SimplexData.map_id]
  rfl

variable (C D : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q

def dgGluingHomTargetCoefficientIntervalEvaluation :
    (Δ[1] : SSet.{max (u + 1) v}) ⊗
      DGNerve.pinchedHom R E (p.obj X.left) (q.obj Y.right) ⟶ dgNerve R E :=
  intervalMappingUncurry (pinchedHomToIntervalMappingSpace (X := dgNerve R E)
    (Simplex.vertex (p.obj X.left)) (Simplex.vertex (q.obj Y.right)))

attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetPostNormalizeCube_canonical_face :
    (Δ[1] ◁ (Δ[1] ◁ prismEndpoint 0
      (complexPinchedSpace.{u, max (u + 1) v} (dgGluingHomComplex R C D M X Y)))) ≫
        dgGluingHomTargetPostNormalizeCube R C D E p q X Y =
    dgGluingPrismIntervalSquare (dgGluingHomTargetNormalizedPrism R C D E p q X Y)
      (dgGluingHomTargetCoefficientIntervalEvaluation R E C D p q X Y) := by
  rw [dgGluingHomTargetPostNormalizeCube, ← Category.assoc,
    dgGluingIdentityCommaPostNormalizeCube_interval_zero,
    dgGluingHomTargetNormalizationHomInput_normalized,
    ← dgGluingHomTargetNormalizedPinchedInput_raw, Category.assoc,
    dgGluingIdentityCommaAugmentationPrism_down]
  have h := dgGluingIdentityCommaPrismInterval_square R E (p.obj X.left) (q.obj Y.right)
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨β, t, s⟩
  let a := (dgGluingHomTargetNormalizedPinchedInput R C D E p q X Y).app
    (Opposite.op ⦋n⦌) s
  exact congrArg (fun k : (Δ[1] : SSet.{max (u + 1) v}) ⊗
      (Δ[1] ⊗ DGNerve.pinchedHom R (DGFunctorCommaObject R E E (DGFunctor.id E))
        (dgGluingIdentityCommaObject R E (p.obj X.left))
        (dgGluingIdentityCommaObject R E (q.obj Y.right))) ⟶ dgNerve R E =>
      k.app (Opposite.op ⦋n⦌) (β, (t, a))) h

end SerrePositivity.InfinityCategories
