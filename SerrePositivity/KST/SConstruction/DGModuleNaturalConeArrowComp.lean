module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalCone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleStrictNatTrans
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransAlgebra

/-!
概要：全厳密比較の合成を元の同じ閉加群射の合成として回収する。
方針：既存の厳密合成の閉零 cycle を元の閉射・閉元対応へ戻す。
規約：全自然性を通常の成分自然性で代用しない。
使われ方：元回転比較と右包含の全合成を cone descent の指定終辺にする。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
private lemma cycleCompose {M N T : ModuleCategory R D} (f : M ⟶ N) (g : N ⟶ T) :
    compose R (x := ForgetEnrichment.to (Complex R) M)
      (y := ForgetEnrichment.to (Complex R) N) (z := ForgetEnrichment.to (Complex R) T)
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) g)).val
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val (zero_add 0) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (f ≫ g))).val :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomPostcompose_apply R D g
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val).symm.trans
      (moduleHomCycle_postcompose R D f g)

variable {P : Type w} [DGCategory R P]
  (F G H : DGFunctor R P (RightModule R D))
  (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G H)

/-- 概要：元全厳密比較の同じ合成閉射は元二閉射の通常順合成。
方針：同じ二 cycle の回収と既存の全厳密合成の成分を照合する。
規約：元二比較を変更しない。使われ方：全 cone 比較の指定終辺回収。 -/
lemma dgModuleNaturalConeArrow_comp (x : P) :
    dgModuleNaturalConeArrow R D F H (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp η θ) x =
      dgModuleNaturalConeArrow R D F G η x ≫ dgModuleNaturalConeArrow R D G H θ x := by
  apply (closedHomEquiv R (RightModule R D) _ _).injective
  apply Subtype.ext
  exact (dgModuleNaturalConeArrow_cycle R D F H (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp η θ) x).trans
    ((congrArg₂ (fun (g : GradedHom R (G.obj x) (H.obj x) 0)
        (f : GradedHom R (F.obj x) (G.obj x) 0) => compose R g f (zero_add 0))
      (dgModuleNaturalConeArrow_cycle R D G H θ x).symm
      (dgModuleNaturalConeArrow_cycle R D F G η x).symm).trans
        (cycleCompose R D (dgModuleNaturalConeArrow R D F G η x)
          (dgModuleNaturalConeArrow R D G H θ x)))
end SerrePositivity.KST.SConstruction
