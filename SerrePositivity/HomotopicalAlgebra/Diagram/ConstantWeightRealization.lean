module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ConstantWeightHom
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # A constant representable weight realizes to the degreewise colimit

This isomorphism uses the actual weight-realization adjunction, simplicial
Yoneda and the actual colimit/constant adjunction. It imposes no model,
cofibrancy or enrichment assumptions.
-/

@[expose] public section
universe w u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.DiagramModel.ConstantWeightRealization
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{w} C]
  [HasColimitsOfSize.{w, w} C] (A : K ⥤ SimplexCategory ⥤ C) (n : SimplexCategory)

/-- Both representing objects give the same actual maps into every Y. -/
def homEquiv (Y : C) :
    ((FrameWeightRealization.functor K A).obj (ConstantWeightHom.weight K n) ⟶ Y) ≃
      (colimit (ConstantWeightHom.degree K A n) ⟶ Y) :=
  ((FrameWeightRealization.adjunction K A).homEquiv _ Y).trans
    ((ConstantWeightHom.homEquiv K A n Y).trans
      ((colimConstAdj (J := K) (C := C)).homEquiv _ Y).symm)

lemma homEquiv_target_naturality {Y Z : C} (f : Y ⟶ Z)
    (a : (FrameWeightRealization.functor K A).obj (ConstantWeightHom.weight K n) ⟶ Y) :
    homEquiv K A n Z (a ≫ f) = homEquiv K A n Y a ≫ f := by
  dsimp [homEquiv]
  rw [Adjunction.homEquiv_naturality_right,
    ConstantWeightHom.homEquiv_target_naturality,
    Adjunction.homEquiv_naturality_right_symm]

/-- Yoneda upgrades the natural Hom equivalence to an actual object isomorphism. -/
def coyonedaIso :
    coyoneda.obj (Opposite.op ((FrameWeightRealization.functor K A).obj
      (ConstantWeightHom.weight K n))) ≅
        coyoneda.obj (Opposite.op (colimit (ConstantWeightHom.degree K A n))) :=
  NatIso.ofComponents (fun Y => Equiv.toIso (homEquiv K A n Y)) (by
    intro Y Z f
    ext a
    exact homEquiv_target_naturality K A n f a)

def iso : (FrameWeightRealization.functor K A).obj (ConstantWeightHom.weight K n) ≅
    colimit (ConstantWeightHom.degree K A n) :=
  (Coyoneda.fullyFaithful.preimageIso (coyonedaIso K A n)).unop.symm

/-- The monoidal unit is the standard zero-simplex, by their actual terminal properties. -/
def unitSimplexIso : (𝟙_ SSet.{w}) ≅ SSet.stdSimplex.obj (SimplexCategory.mk 0) :=
  CartesianMonoidalCategory.isTerminalTensorUnit.uniqueUpToIso SSet.stdSimplex.isTerminalObj₀

abbrev unitWeight : Kᵒᵖ ⥤ SSet.{w} := (Functor.const Kᵒᵖ).obj (𝟙_ SSet.{w})

def unitIso : (FrameWeightRealization.functor K A).obj (unitWeight K) ≅
    colimit (ConstantWeightHom.degree K A (SimplexCategory.mk 0)) :=
  (FrameWeightRealization.functor K A).mapIso
    ((Functor.const Kᵒᵖ).mapIso unitSimplexIso) ≪≫ iso K A (SimplexCategory.mk 0)

/-- The ordinary comparison exists for every augmented weight; no weak-equivalence
assertion about a noncofibrant constant weight is part of this construction. -/
def comparison {W : Kᵒᵖ ⥤ SSet.{w}} (q : W ⟶ unitWeight K) :
    (FrameWeightRealization.functor K A).obj W ⟶
      colimit (ConstantWeightHom.degree K A (SimplexCategory.mk 0)) :=
  (FrameWeightRealization.functor K A).map q ≫ (unitIso K A).hom

end SerrePositivity.DiagramModel.ConstantWeightRealization
