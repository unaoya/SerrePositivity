module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarEvaluation

/-! # 係数変更したHom因子と実際の係数変更dg圏のHomの比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] (E : D)

lemma endomorphismScalarForward_one {x y z : D} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (hn : p + q = n) :
    let := φ.toAlgebra
    forward A' (D := ScalarExtension.DGBaseChange φ D)
        ((1 : A') ⊗ₜ[A] f) ((1 : A') ⊗ₜ[A] g) hn =
      (1 : A') ⊗ₜ[A] forward A f g hn := by
  let := φ.toAlgebra
  change ((ScalarExtension.extension φ).map (eComp (Complex A) x y z)).f n
    ((ScalarExtension.tensorIso φ (homObject A D x y) (homObject A D y z)).inv.f n
      (ιTensorObj ((ScalarExtension.extension φ).obj (homObject A D x y))
        ((ScalarExtension.extension φ).obj (homObject A D y z)) p q n hn
        (((1 : A') ⊗ₜ[A] f) ⊗ₜ[A'] ((1 : A') ⊗ₜ[A] g)))) = _
  erw [ScalarExtension.tensorIso_inv_apply, ModuleCat.ExtendScalars.map_tmul φ]
  rfl

/-- 係数変更先dg圏の実際のYonedaを、係数変更した指定対象の包含へ制限する。 -/
def endomorphismBaseChangeHomRight (Y : D) :
    RightModule A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E)) :=
  restrictModule A' _ _ (ScalarExtension.dgFunctor φ (endomorphismInclusion A E)).op
    (representable A' (show ScalarExtension.DGBaseChange φ D from Y))

lemma endomorphismScalarHomRight_eq (Y : D) :
    ScalarExtension.rightModule φ (EndomorphismObject E) (endomorphismHomRight A D E Y) =
      endomorphismBaseChangeHomRight φ D E Y := by
  let := φ.toAlgebra
  apply EnrichedFunctor.ext (Complex A')
    (F := (ScalarExtension.rightModule φ (EndomorphismObject E)
      (endomorphismHomRight A D E Y)).toFunctor)
    (G := (endomorphismBaseChangeHomRight φ D E Y).toFunctor) (fun _ => rfl)
  intro x y
  cases x
  cases y
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.hom_ext
  intro p
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Cochain.ext
  intro r n hn
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change ((ScalarExtension.homComparison φ (homObject A D E Y) (homObject A D E Y)).f p
    ((ModuleCat.extendScalars φ).map
      (((endomorphismHomRight A D E Y).map (op .point) (op .point)).f p)
      ((1 : A') ⊗ₜ[A] f))).v r n hn ((1 : A') ⊗ₜ[A] m) = _
  erw [ModuleCat.ExtendScalars.map_tmul φ, ScalarExtension.homComparison_apply]
  change (1 : A') ⊗ₜ[A] forward A (D := D) (x := E) (y := E) (z := Y) f m (by omega) =
    forward A' (D := ScalarExtension.DGBaseChange φ D)
      (x := E) (y := E) (z := Y) ((1 : A') ⊗ₜ[A] f) ((1 : A') ⊗ₜ[A] m) (by omega)
  exact (endomorphismScalarForward_one φ D f m (by omega)).symm

/-- 係数変更先dg圏の実際の左Yonedaを、係数変更した包含へ制限する。 -/
def endomorphismBaseChangeHomLeft (X : D) :
    LeftModule A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E)) :=
  (ScalarExtension.dgFunctor φ (endomorphismInclusion A E)).comp
    (leftRepresentable A' (show ScalarExtension.DGBaseChange φ D from X))

lemma endomorphismScalarHomLeft_eq (X : D) :
    ScalarExtension.leftModule φ (EndomorphismObject E) (endomorphismHomLeft A D E X) =
      endomorphismBaseChangeHomLeft φ D E X := by
  let := φ.toAlgebra
  apply EnrichedFunctor.ext (Complex A')
    (F := ScalarExtension.leftModule φ (EndomorphismObject E) (endomorphismHomLeft A D E X))
    (G := endomorphismBaseChangeHomLeft φ D E X) (fun _ => rfl)
  intro x y
  cases x
  cases y
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.hom_ext
  intro p
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Cochain.ext
  intro r n hn
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change ((ScalarExtension.homComparison φ (homObject A D X E) (homObject A D X E)).f p
    ((ModuleCat.extendScalars φ).map
      (((endomorphismHomLeft A D E X).map .point .point).f p)
      ((1 : A') ⊗ₜ[A] f))).v r n hn ((1 : A') ⊗ₜ[A] m) = _
  erw [ModuleCat.ExtendScalars.map_tmul φ, ScalarExtension.homComparison_apply]
  change (1 : A') ⊗ₜ[A] leftAction A (leftRepresentable A X) f m hn =
    leftAction A' (leftRepresentable A' (show ScalarExtension.DGBaseChange φ D from X))
      ((1 : A') ⊗ₜ[A] f) ((1 : A') ⊗ₜ[A] m) hn
  have hs := leftRepresentable_action A X E E f m hn
  have ht := leftRepresentable_action A'
    (show ScalarExtension.DGBaseChange φ D from X) E E
    ((1 : A') ⊗ₜ[A] f) ((1 : A') ⊗ₜ[A] m) hn
  rw [hs, ht, endomorphismScalarForward_one]
  simp only [Units.smul_def, TensorProduct.tmul_smul]

lemma endomorphismBaseChangeInclusion_eq :
    ScalarExtension.dgFunctor φ (endomorphismInclusion A E) =
      endomorphismInclusion A' (show ScalarExtension.DGBaseChange φ D from E) := by
  apply EnrichedFunctor.ext (Complex A')
    (F := ScalarExtension.dgFunctor φ (endomorphismInclusion A E))
    (G := endomorphismInclusion A' (show ScalarExtension.DGBaseChange φ D from E))
    (fun _ => rfl)
  intro x y
  simp only [ScalarExtension.dgFunctor, endomorphismInclusion,
    CategoryTheory.Functor.map_id, eqToHom_refl, Category.comp_id]
  rfl

lemma endomorphismBaseChangeHomRight_actual (Y : D) :
    endomorphismBaseChangeHomRight φ D E Y =
      endomorphismHomRight A' (ScalarExtension.DGBaseChange φ D) E Y := by
  unfold endomorphismBaseChangeHomRight
  rw [endomorphismBaseChangeInclusion_eq]
  rfl

lemma endomorphismBaseChangeHomLeft_actual (X : D) :
    endomorphismBaseChangeHomLeft φ D E X =
      endomorphismHomLeft A' (ScalarExtension.DGBaseChange φ D) E X := by
  unfold endomorphismBaseChangeHomLeft
  rw [endomorphismBaseChangeInclusion_eq]
  rfl

def endomorphismScalarHomRightIso (Y : D) :
    ForgetEnrichment.of (Complex A') (ScalarExtension.rightModule φ (EndomorphismObject E)
      (endomorphismHomRight A D E Y)) ≅
    ForgetEnrichment.of (Complex A')
      (endomorphismHomRight A' (ScalarExtension.DGBaseChange φ D) E Y) :=
  eqToIso (congrArg (ForgetEnrichment.of (Complex A'))
    ((endomorphismScalarHomRight_eq φ D E Y).trans
      (endomorphismBaseChangeHomRight_actual φ D E Y)))

def endomorphismScalarHomLeftIso (X : D) :
    ForgetEnrichment.of (Complex A') (ScalarExtension.leftModule φ (EndomorphismObject E)
      (endomorphismHomLeft A D E X)) ≅
    ForgetEnrichment.of (Complex A')
      (endomorphismHomLeft A' (ScalarExtension.DGBaseChange φ D) E X) :=
  eqToIso (congrArg (ForgetEnrichment.of (Complex A'))
    ((endomorphismScalarHomLeft_eq φ D E X).trans
      (endomorphismBaseChangeHomLeft_actual φ D E X)))

lemma endomorphismScalarHomRightIso_hom_eval (Y : D) (b : EndomorphismObject E) :
    (moduleEvaluation A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E)) b).map
      (endomorphismScalarHomRightIso φ D E Y).hom = 𝟙 _ := by
  unfold endomorphismScalarHomRightIso
  rw [eqToIso.hom, eqToHom_map]
  rfl

lemma endomorphismScalarHomLeftIso_hom_eval (X : D) (b : EndomorphismObject E) :
    (leftModuleEvaluation A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E)) b).map
      (endomorphismScalarHomLeftIso φ D E X).hom = 𝟙 _ := by
  unfold endomorphismScalarHomLeftIso
  rw [eqToIso.hom, eqToHom_map]
  rfl

lemma balancedTensorEqIso_ι {B : Type*} [DGCategory A' B] [Small.{u} B]
    {M M' : RightModule A' B} {N N' : LeftModule A' B}
    (hM : M = M') (hN : N = N') (b : B) :
    BalancedTensor.ι A' B M N b ≫
        (eqToIso (congrArg₂ (BalancedTensor.obj A' B) hM hN)).hom =
      (eqToHom (congrArg (fun L : RightModule A' B => L.obj (op b)) hM) ⊗ₘ
        eqToHom (congrArg (fun L : LeftModule A' B => L.obj b) hN)) ≫
          BalancedTensor.ι A' B M' N' b := by
  subst M'
  subst N'
  simp only [eqToIso_refl, Iso.refl_hom, eqToHom_refl, tensorHom_id, id_whiskerRight,
    Category.comp_id, Category.id_comp]

def endomorphismScalarHomTensorIso (X Y : D) :
    BalancedTensor.obj A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
      (ScalarExtension.rightModule φ (EndomorphismObject E) (endomorphismHomRight A D E Y))
      (ScalarExtension.leftModule φ (EndomorphismObject E) (endomorphismHomLeft A D E X)) ≅
    BalancedTensor.obj A' (EndomorphismObject (show ScalarExtension.DGBaseChange φ D from E))
      (endomorphismHomRight A' (ScalarExtension.DGBaseChange φ D) E Y)
      (endomorphismHomLeft A' (ScalarExtension.DGBaseChange φ D) E X) :=
  eqToIso (congrArg₂ (BalancedTensor.obj A'
    (ScalarExtension.DGBaseChange φ (EndomorphismObject E)))
      ((endomorphismScalarHomRight_eq φ D E Y).trans
        (endomorphismBaseChangeHomRight_actual φ D E Y))
      ((endomorphismScalarHomLeft_eq φ D E X).trans
        (endomorphismBaseChangeHomLeft_actual φ D E X)))

lemma endomorphismScalarHomTensorIso_ι (X Y : D) (b : EndomorphismObject E) :
    BalancedTensor.ι A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
        (ScalarExtension.rightModule φ (EndomorphismObject E) (endomorphismHomRight A D E Y))
        (ScalarExtension.leftModule φ (EndomorphismObject E) (endomorphismHomLeft A D E X)) b ≫
      (endomorphismScalarHomTensorIso φ D E X Y).hom =
    BalancedTensor.ι A' (EndomorphismObject (show ScalarExtension.DGBaseChange φ D from E))
      (endomorphismHomRight A' (ScalarExtension.DGBaseChange φ D) E Y)
      (endomorphismHomLeft A' (ScalarExtension.DGBaseChange φ D) E X) b := by
  unfold endomorphismScalarHomTensorIso
  rw [balancedTensorEqIso_ι
    ((endomorphismScalarHomRight_eq φ D E Y).trans
      (endomorphismBaseChangeHomRight_actual φ D E Y))
    ((endomorphismScalarHomLeft_eq φ D E X).trans
      (endomorphismBaseChangeHomLeft_actual φ D E X))]
  change (𝟙 _ ⊗ₘ 𝟙 _) ≫ _ = _
  rw [tensorHom_id, id_whiskerRight]
  exact Category.id_comp _

end SerrePositivity.DifferentialGraded
