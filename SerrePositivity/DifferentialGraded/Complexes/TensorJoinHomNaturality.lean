module
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainNaturality
public import SerrePositivity.DifferentialGraded.Complexes.HomMapEvaluation

/-! # 前方二因子の合成に関する全Hom写像の自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma tensorJoin_hom_naturality (U V W P Q : Complex A) (c : U ⊗ V ⟶ W) :
    (tensorLeftHom V P Q ≫ tensorLeftHom U (V ⊗ P) (V ⊗ Q)) ≫
      homPostcompose (U ⊗ (V ⊗ P)) ((α_ U V Q).inv ≫ c ▷ Q) =
    tensorLeftHom W P Q ≫
      homPrecompose ((α_ U V P).inv ≫ c ▷ P) (W ⊗ Q) := by
  apply hom_naturality_of_apply
  intro p f
  exact (tensorJoin_cochain_naturality U V W P Q c p f).symm

end SerrePositivity.DifferentialGraded
