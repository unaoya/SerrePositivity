module

public import SerrePositivity.EInfinity.PowerOperation.ComplexRelativeElementSourceRoof
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveHomLiftIso
public import SerrePositivity.EInfinity.ComplexLimits.DerivedNatTransComponent

/-!
# 全複体の相対列の通常の導来源での全自然変換の回収

DAG XIII §2.2 の native な降下の補助。同じ全射列と通常円柱を保持し、
Hom 宇宙の持ち上げを戻す。［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet MonoidalClosed
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
open FunctorCategories
open _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories (derivedInfinityCategory)
variable (A : Type u) [CommRing A]

/-- 同じ複体の Hom だけを上げた表示から、元の相対圏への全関手。 -/
def complexHomLiftToRelative : ULiftHom.{u + 1} (Complex A) ⥤
    (complexRelativeCategory A).category :=
  ULiftHom.down.{u, u + 1, u + 1} ⋙ complexRelativeUp A

lemma complexRelativeDerivedSource_onHomLift :
    nerveMap (complexHomLiftToRelative A) ≫ complexRelativeDerivedSource A =
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down (Complex A) ≫ complexOrdinaryDerivedSource A := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Γ
  apply congrArg ((complexOrdinaryDerivedSource A).app n)
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 同じ相対列の円柱の像は、元の通常複体円柱の全制限である。 -/
lemma complexRelativeColumnHom_arrow {I : Type (u + 1)} [Category.{u} I]
    {V W : I ⥤ Complex A} (a : V ⟶ W) :
    Arrow.mk (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom (complexRelativeDerivedSource A)
      (Functor.whiskerRight (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.liftedNatTrans a) (complexHomLiftToRelative A))) =
      Arrow.mk ((hoFunctor.map ((pre (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down I)).app
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))).toFunctor.map (complexOrdinaryDerivedNatTransHom A a)) := by
  have h₁ := congrArg Arrow.mk
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom_whiskerRight (complexHomLiftToRelative A)
      (complexRelativeDerivedSource A) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.liftedNatTrans a)).symm
  have h₂ := congrArg (fun F : nerve (ULiftHom.{u + 1} (Complex A)) ⟶
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A => Arrow.mk (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom F (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.liftedNatTrans a)))
    (complexRelativeDerivedSource_onHomLift A)
  exact h₁.trans (h₂.trans
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.liftedHom_postcomp_arrow I a (complexOrdinaryDerivedSource A)))

end SerrePositivity.EInfinity.PowerOperation
