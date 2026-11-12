module

public import SerrePositivity.HomotopicalAlgebra.SmallHomModel
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Realization
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation

/-! # Frame realization in the local-presentability universe

The original category has independent object, Hom and accessibility
universes. Passing through Mathlib's existing ShrinkHoms equivalence gives
an actual realization SSet(w) ⥤ C using only the colimits supplied by local
presentability in w. Its right adjoint is the actual small-Hom frame functor.
After explicit universe lifts it is naturally isomorphic to ordinary
cosimplicial Hom in the original Hom universe.
-/

@[expose] public section
universe w v u vH uH
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.SmallHomRealization
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]

local instance : HasColimitsOfSize.{0, w} (ShrinkHoms C) :=
  SmallHomModel.realizationColimits.{w} C

abbrev frame (A : SimplexCategory ⥤ C) : SimplexCategory ⥤ ShrinkHoms C :=
  A ⋙ (SmallHomModel.equivalence.{w} C).inverse

abbrev hom (A : SimplexCategory ⥤ C) : C ⥤ SSet.{w} :=
  (SmallHomModel.equivalence.{w} C).inverse ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (frame A)

abbrev functor (A : SimplexCategory ⥤ C) : SSet.{w} ⥤ C :=
  Realization.functor (frame A) ⋙ (SmallHomModel.equivalence.{w} C).functor

def adjunction (A : SimplexCategory ⥤ C) : functor A ⊣ hom A :=
  (Realization.adjunction (frame A)).comp (SmallHomModel.equivalence.{w} C).toAdjunction

instance functor_isLeftAdjoint (A : SimplexCategory ⥤ C) : (functor A).IsLeftAdjoint :=
  (adjunction A).isLeftAdjoint

/-- Changing the Hom representation and returning is naturally the original frame. -/
def frameIso (A : SimplexCategory ⥤ C) :
    frame A ⋙ (SmallHomModel.equivalence.{w} C).functor ≅ A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft A (SmallHomModel.equivalence.{w} C).counitIso ≪≫ Functor.rightUnitor A

/-- This is an actual natural simplicial isomorphism in the common universe. -/
def homLiftIso (A : SimplexCategory ⥤ C) :
    hom A ⋙ SSet.uliftFunctor.{v,w} ≅ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A ⋙ SSet.uliftFunctor.{w,v} :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.adjunctionHomIso (SmallHomModel.equivalence.{w} C).toAdjunction (frame A)).symm ≪≫
    Functor.isoWhiskerRight (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor.mapIso (frameIso A).symm.op)
      SSet.uliftFunctor.{w,v}

lemma frame_reedyCofibrant (A : SimplexCategory ⥤ C)
    (hA : reedyLeft simplex (cofibrations C) (initial.to A)) :
    let := SmallHomModel.modelCategory.{w} C
    reedyLeft simplex (cofibrations (ShrinkHoms C)) (initial.to (frame A)) := by
  let := SmallHomModel.modelCategory.{w} C
  have := SmallHomModel.fromOriginal_isLeftQuillen.{w} C
  have : (SmallHomModel.equivalence.{w} C).inverse.IsLeftAdjoint :=
    (SmallHomModel.equivalence.{w} C).symm.toAdjunction.isLeftAdjoint
  exact leftQuillen_frame_reedyCofibrant (SmallHomModel.equivalence.{w} C).inverse A hA

lemma frame_homotopicallyConstant (A : SimplexCategory ⥤ C)
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))
    {n m : SimplexCategory} (f : n ⟶ m) :
    let := SmallHomModel.modelCategory.{w} C
    weakEquivalences (ShrinkHoms C) ((frame A).map f) := by
  let := SmallHomModel.modelCategory.{w} C
  have := SmallHomModel.fromOriginal_isLeftQuillen.{w} C
  exact leftQuillen_frame_homotopicallyConstant (SmallHomModel.equivalence.{w} C).inverse
    A hA hconst f

variable [ModelCategory SSet.{w}]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (A : SimplexCategory ⥤ C)
  (hA : reedyLeft simplex (cofibrations C) (initial.to A))
  (hconst : ∀ {n m : SimplexCategory} (f : n ⟶ m), weakEquivalences C (A.map f))

include hcof hfib hA hconst

/-- Local presentability in w suffices; no v-sized colimit assumption remains. -/
lemma isLeftQuillen : Quillen.IsLeftQuillen (functor A) := by
  let := SmallHomModel.modelCategory.{w} C
  have := Realization.isLeftQuillen hcof hfib (frame A)
    (frame_reedyCofibrant A hA) (frame_homotopicallyConstant A hA hconst)
  have := SmallHomModel.toOriginal_isLeftQuillen.{w} C
  exact Quillen.isLeftQuillen_comp _ _

lemma isRightQuillen : Quillen.IsRightQuillen (hom A) := by
  have := isLeftQuillen hcof hfib A hA hconst
  exact (Quillen.isLeftQuillen_iff_isRightQuillen (adjunction A)).mp inferInstance

lemma hasPointwiseLeftDerived {H : Type uH} [Category.{vH} H]
    (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)] :
    (functor A ⋙ L).HasPointwiseLeftDerivedFunctor (weakEquivalences SSet.{w}) := by
  have := isLeftQuillen hcof hfib A hA hconst
  infer_instance

end SerrePositivity.HomotopyFunctionComplex.SmallHomRealization
