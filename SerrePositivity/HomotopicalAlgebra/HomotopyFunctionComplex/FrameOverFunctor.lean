module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameComparison

/-! # Comparing frames augmented over an arbitrary functor

The parameter category B need not itself be a model category. Both source
families are augmented over H : B ⥤ C, rather than only over the identity
of C. The pullback and its actual Reedy cofibrant replacement give natural
weak comparison maps; applying Hom gives a two-variable natural cospan.
-/

@[expose] public section
universe v u vB uB
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.FrameOverFunctor
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {B : Type uB} [Category.{vB} B]
local instance : ModelCategory (SimplexCategory ⥤ C) := simplexModelCategory C
variable
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (q : CofibrantResolutionFamily (C := C) simplex) (H : B ⥤ C)
  (P : B ⥤ (SimplexCategory ⥤ C)) (a : P ⟶ H ⋙ Functor.const SimplexCategory)

abbrev resolution : B ⥤ (SimplexCategory ⥤ C) := H ⋙ q.obj
abbrev resolutionAugmentation : resolution q H ⟶ H ⋙ Functor.const SimplexCategory :=
  Functor.whiskerLeft H q.augmentation

abbrev commonObj : B ⥤ (SimplexCategory ⥤ C) := ModelReplacement.CommonCofibrant.obj
  (ResolutionComparison.diagramCofFactorization cof) (resolutionAugmentation q H) a

abbrev left : commonObj cof q H P a ⟶ resolution q H := ModelReplacement.CommonCofibrant.left
  (ResolutionComparison.diagramCofFactorization cof) (resolutionAugmentation q H) a

abbrev right : commonObj cof q H P a ⟶ P := ModelReplacement.CommonCofibrant.right
  (ResolutionComparison.diagramCofFactorization cof) (resolutionAugmentation q H) a

lemma over : left cof q H P a ≫ resolutionAugmentation q H = right cof q H P a ≫ a :=
  ModelReplacement.CommonCofibrant.over
    (ResolutionComparison.diagramCofFactorization cof) (resolutionAugmentation q H) a

lemma commonObj_cofibrant (X : B) :
    reedyLeft simplex (cofibrations C) (initial.to ((commonObj cof q H P a).obj X)) := by
  have := ModelReplacement.CommonCofibrant.isCofibrant_obj
    (ResolutionComparison.diagramCofFactorization cof) (resolutionAugmentation q H) a X
  exact mem_cofibrations (initial.to ((commonObj cof q H P a).obj X))

lemma right_weakEquivalence (X : B) (n : SimplexCategory) :
    weakEquivalences C (((right cof q H P a).app X).app n) :=
  (ModelReplacement.CommonCofibrant.right_trivialFibration
    (ResolutionComparison.diagramCofFactorization cof) (resolutionAugmentation q H) a
    (fun X => ResolutionComparison.augmentation_trivialFibration q (H.obj X)) X).2 n

lemma left_weakEquivalence (ha : ∀ X n, weakEquivalences C ((a.app X).app n))
    (X : B) (n : SimplexCategory) :
    weakEquivalences C (((left cof q H P a).app X).app n) := by
  have h := congr_app (congr_app (over cof q H P a) X) n
  change ((left cof q H P a).app X).app n ≫ (q.augmentation.app (H.obj X)).app n =
    ((right cof q H P a).app X).app n ≫ (a.app X).app n at h
  exact (weakEquivalences C).of_postcomp _ _ ((q.atObject (H.obj X)).augmentation_weakEquivalence n)
    (h.symm ▸ (weakEquivalences C).comp_mem _ _ (right_weakEquivalence cof q H P a X n) (ha X n))

/-- Actual Hom, functorial in an independent source parameter and the target. -/
abbrev hom (A : B ⥤ (SimplexCategory ⥤ C)) : Bᵒᵖ ⥤ C ⥤ SSet.{v} :=
  A.op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor

abbrev homLeft : hom (resolution q H) ⟶ hom (commonObj cof q H P a) :=
  Functor.whiskerRight (NatTrans.op (left cof q H P a)) _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor

abbrev homRight : hom P ⟶ hom (commonObj cof q H P a) :=
  Functor.whiskerRight (NatTrans.op (right cof q H P a)) _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor

lemma commonObj_homotopicallyConstant
    (ha : ∀ X n, weakEquivalences C ((a.app X).app n))
    (X : B) {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences C (((commonObj cof q H P a).obj X).map f) := by
  let aug := right cof q H P a ≫ a
  have hw (t : SimplexCategory) : weakEquivalences C ((aug.app X).app t) :=
    (weakEquivalences C).comp_mem _ _ (right_weakEquivalence cof q H P a X t) (ha X t)
  have he := (aug.app X).naturality f
  change ((commonObj cof q H P a).obj X).map f ≫ (aug.app X).app m =
    (aug.app X).app n ≫ 𝟙 (H.obj X) at he
  exact (weakEquivalences C).of_postcomp _ _ (hw m)
    ((he.trans (Category.comp_id _)).symm ▸ hw n)

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma homLeft_weakEquivalence (ha : ∀ X n, weakEquivalences C ((a.app X).app n))
    (X : Bᵒᵖ) (Y : C) [IsFibrant Y] :
    weakEquivalences SSet.{v} (((homLeft cof q H P a).app X).app Y) :=
  cosimplicialHomMap_weakEquivalence hcof ((left cof q H P a).app X.unop)
    (commonObj_cofibrant cof q H P a X.unop) (q.cofibrant (H.obj X.unop))
    (left_weakEquivalence cof q H P a ha X.unop) Y

include hcof in
lemma homRight_weakEquivalence
    (hP : ∀ X, reedyLeft simplex (cofibrations C) (initial.to (P.obj X)))
    (X : Bᵒᵖ) (Y : C) [IsFibrant Y] :
    weakEquivalences SSet.{v} (((homRight cof q H P a).app X).app Y) :=
  cosimplicialHomMap_weakEquivalence hcof ((right cof q H P a).app X.unop)
    (commonObj_cofibrant cof q H P a X.unop) (hP X.unop)
    (right_weakEquivalence cof q H P a X.unop) Y

end SerrePositivity.HomotopyFunctionComplex.FrameOverFunctor
