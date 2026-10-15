module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ConstantWeightRealization
public import SerrePositivity.HomotopicalAlgebra.Diagram.SmallHomFrameWeights
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # Constant weight realization in independent Hom and presentability universes

The constant-weight isomorphism is transported through the existing small
Hom equivalence and its actual colimit preservation isomorphism. The
result lies in the original C, with no relation between its Hom universe
and the weight universe.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.DiagramModel.SmallHomConstantWeight
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [HomotopicalAlgebra.ModelCategory C] [IsLocallyPresentable.{w} C]

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)
local instance : HasColimitsOfSize.{w, w} (ShrinkHoms C) := by
  have := SmallHomModel.locallyPresentable.{w} C
  exact Smith.locallyPresentable_hasColimits (C := ShrinkHoms C)

variable (A : K ⥤ SimplexCategory ⥤ C) (n : SimplexCategory)

def degreeIso : ConstantWeightHom.degree K (SmallHomFrameWeights.source K A) n ⋙
    (SmallHomModel.equivalence.{w} C).functor ≅ ConstantWeightHom.degree K A n :=
  NatIso.ofComponents (fun k => (SmallHomModel.equivalence.{w} C).counitIso.app ((A.obj k).obj n))
    (by
      intro k l f
      exact (SmallHomModel.equivalence.{w} C).counitIso.hom.naturality ((A.map f).app n))

/-- No model structure on the auxiliary simplicial sets is needed for this object isomorphism. -/
def iso : (SmallHomFrameWeights.functor K A).obj (ConstantWeightHom.weight K n) ≅
    colimit (ConstantWeightHom.degree K A n) := by
  let F := (SmallHomModel.equivalence.{w} C).functor
  have : F.IsLeftAdjoint := (SmallHomModel.equivalence.{w} C).toAdjunction.isLeftAdjoint
  exact F.mapIso (ConstantWeightRealization.iso K (SmallHomFrameWeights.source K A) n) ≪≫
    preservesColimitIso F (ConstantWeightHom.degree K (SmallHomFrameWeights.source K A) n) ≪≫
    HasColimit.isoOfNatIso (degreeIso K A n)

def unitIso : (SmallHomFrameWeights.functor K A).obj (ConstantWeightRealization.unitWeight K) ≅
    colimit (ConstantWeightHom.degree K A (SimplexCategory.mk 0)) :=
  (SmallHomFrameWeights.functor K A).mapIso
    ((Functor.const Kᵒᵖ).mapIso ConstantWeightRealization.unitSimplexIso) ≪≫
      iso K A (SimplexCategory.mk 0)

def comparison {W : Kᵒᵖ ⥤ SSet.{w}} (q : W ⟶ ConstantWeightRealization.unitWeight K) :
    (SmallHomFrameWeights.functor K A).obj W ⟶
      colimit (ConstantWeightHom.degree K A (SimplexCategory.mk 0)) :=
  (SmallHomFrameWeights.functor K A).map q ≫ (unitIso K A).hom

end SerrePositivity.DiagramModel.SmallHomConstantWeight
