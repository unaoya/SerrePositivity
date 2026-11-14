module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.Kernels.KernelColumnHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.EnrichedFunctors.EnrichedMiddleComposition

/-! 列比較の逆射の全 Hom 自然性と、係数 Hom の合成との整合。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
local notation "F" => Morita.kernelTensor R D C M
local notation "col" d =>
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso R C D M (ForgetEnrichment.of (Complex R) d)

/-- 列比較の逆射も、全整数次数の Hom 写像と厳密に可換する。 -/
lemma dgGluingKernelColumnIso_inv_naturality (d d' : D) :
    M.toFunctor.map d d' ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (M.rightAt d)) (col d').inv =
    yonedaHom R D d d' ≫ (F).map (representable R d) (representable R d') ≫
      eHomWhiskerRight (Complex R) (col d).inv
        (ForgetEnrichment.of (Complex R) ((F).obj (representable R d'))) := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelColumnIso_hom_naturality R C D M d d'
  rw [← Category.assoc] at hn
  have he := congrArg (fun k => k ≫
    eHomWhiskerRight (Complex R) (col d).inv
      (ForgetEnrichment.of (Complex R) (M.rightAt d')) ≫
    eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (M.rightAt d)) (col d').inv) hn
  simp only [Category.assoc] at he
  erw [eHom_whisker_exchange_assoc (Complex R) (col d).inv (col d').hom] at he
  erw [← eHomWhiskerLeft_comp (Complex R)
    (ForgetEnrichment.of (Complex R) (M.rightAt d)) (col d').hom (col d').inv] at he
  erw [← eHomWhiskerRight_comp_assoc (Complex R) (col d).inv (col d).hom
    (ForgetEnrichment.of (Complex R) (M.rightAt d'))] at he
  simp only [Iso.inv_hom_id, Iso.hom_inv_id, eHomWhiskerLeft_id, eHomWhiskerRight_id,
    Category.id_comp] at he
  exact he.symm

/-- 任意の左加群からの係数 Hom の合成は、列比較の逆射と可換する。 -/
lemma dgGluingKernelColumnIso_inv_composition
    (P : ClosedCategory R (RightModule R C)) (d d' : D) :
    (eHomWhiskerLeft (Complex R) P (col d).inv ⊗ₘ
      (yonedaHom R D d d' ≫ (F).map (representable R d) (representable R d'))) ≫
      eComp (Complex R) P
        (ForgetEnrichment.of (Complex R) ((F).obj (representable R d)))
        (ForgetEnrichment.of (Complex R) ((F).obj (representable R d'))) =
    (𝟙 _ ⊗ₘ M.toFunctor.map d d') ≫
      eComp (Complex R) P (ForgetEnrichment.of (Complex R) (M.rightAt d))
        (ForgetEnrichment.of (Complex R) (M.rightAt d')) ≫
      eHomWhiskerLeft (Complex R) P (col d').inv := by
  rw [eComp_eHomWhiskerLeft, ← Category.assoc, tensorHom_comp_whiskerLeft,
    dgGluingKernelColumnIso_inv_naturality]
  simp only [tensorHom_def', MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.id_whiskerRight, Category.comp_id, Category.assoc]
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedComposition_middle (Complex R) (ClosedCategory R (RightModule R C)) P
    (ForgetEnrichment.of (Complex R) (M.rightAt d))
    (ForgetEnrichment.of (Complex R) ((F).obj (representable R d)))
    (ForgetEnrichment.of (Complex R) ((F).obj (representable R d'))) (col d).inv]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
