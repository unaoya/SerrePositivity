module

public import SerrePositivity.DifferentialGraded.Endomorphism.Derived.Functors
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.CategoriesAndModules
public import SerrePositivity.DifferentialGraded.Module.Yoneda
public import SerrePositivity.DifferentialGraded.Module.HomFunctor
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.Algebra.Homology.QuasiIso
public import SerrePositivity.DifferentialGraded.Module.Homotopy
public import SerrePositivity.DifferentialGraded.Functor.Components
public import SerrePositivity.DifferentialGraded.Module.Precomposition

/-!
# Endomorphism.Scalar.HomComparison

## 概要
実際の係数拡大による全次数 Hom 比較・Yoneda・retract 自然性をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

universe u v w w'

/-! ## IsoLocus（旧 SerrePositivity/DifferentialGraded/Endomorphism/IsoLocus.lean） -/

/-! # 恒等関手からのshift整合的自然変換の同型性の閉性 -/

@[expose] public section IsoLocus

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (G : DerivedModuleCategory A D ⥤ DerivedModuleCategory A D)
variable (α : 𝟭 (DerivedModuleCategory A D) ⟶ G)

def derivedNatTransIsoLocus : ObjectProperty (DerivedModuleCategory A D) :=
  fun X => IsIso (α.app X)

instance derivedNatTransIsoLocus_closedIso :
    (derivedNatTransIsoLocus A D G α).IsClosedUnderIsomorphisms where
  of_iso e hX := by
    change IsIso (α.app _) at hX ⊢
    let := hX
    have he : α.app _ = e.inv ≫ α.app _ ≫ G.map e.hom := by
      rw [← α.naturality]
      simp
    rw [he]
    infer_instance

variable [G.CommShift ℤ] [G.IsTriangulated] [G.Additive] [NatTrans.CommShift α ℤ]

instance derivedNatTransIsoLocus_shift :
    (derivedNatTransIsoLocus A D G α).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨by
    intro X hX
    change IsIso (α.app X) at hX
    let := hX
    change IsIso (α.app (X⟦n⟧))
    rw [NatTrans.app_shift α]
    infer_instance⟩

instance derivedNatTransIsoLocus_containsZero :
    (derivedNatTransIsoLocus A D G α).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, by
    change IsIso (α.app 0)
    exact (isZero_zero _).isIso (G.map_isZero (isZero_zero _)) _⟩

instance derivedNatTransIsoLocus_closedTriangle :
    (derivedNatTransIsoLocus A D G α).IsTriangulatedClosed₃ := by
  apply ObjectProperty.IsTriangulatedClosed₃.mk'
  intro T hT h₁ h₂
  change IsIso (α.app T.obj₁) at h₁
  change IsIso (α.app T.obj₂) at h₂
  change IsIso (α.app T.obj₃)
  let φ : T ⟶ G.mapTriangle.obj T := {
    hom₁ := α.app T.obj₁
    hom₂ := α.app T.obj₂
    hom₃ := α.app T.obj₃
    comm₁ := α.naturality T.mor₁
    comm₂ := α.naturality T.mor₂
    comm₃ := by
      dsimp
      rw [← α.naturality_assoc, ← NatTrans.shift_app_comm]
      simp }
  exact isIso₃_of_isIso₁₂ φ hT (G.map_distinguished T hT) h₁ h₂

instance derivedNatTransIsoLocus_triangulated :
    (derivedNatTransIsoLocus A D G α).IsTriangulated where
  toIsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

omit [G.CommShift ℤ] [G.IsTriangulated] [G.Additive] [NatTrans.CommShift α ℤ] in
lemma derivedNatTransIsoLocus_coproduct {J : Type u}
    (F : J → DerivedModuleCategory A D) [PreservesColimit (Discrete.functor F) G]
    (hF : ∀ j, derivedNatTransIsoLocus A D G α (F j)) :
    derivedNatTransIsoLocus A D G α (∐ F) := by
  let (j : J) : IsIso (α.app (F j)) := hF j
  have h : Limits.Sigma.map (fun j => α.app (F j)) ≫ sigmaComparison G F = α.app (∐ F) := by
    apply Sigma.hom_ext
    intro j
    simp only [Limits.Sigma.ι_map_assoc, ι_comp_sigmaComparison]
    exact (α.naturality (Sigma.ι F j)).symm
  change IsIso (α.app (∐ F))
  rw [← h]
  infer_instance

end SerrePositivity.DifferentialGraded
end

end IsoLocus

/-! ## ScalarEvaluation（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarEvaluation.lean） -/

/-! # balanced合成評価の係数変更と導来比較射の可換性

係数変更したHom因子をそのまま保持する。実際の係数変更先のHomとの同型性は主張しない。
-/

@[expose] public section ScalarEvaluation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] (E X Y : D)

/-- 係数変更したHom因子上の評価。coendの係数変更同型を介して定める。 -/
def endomorphismScalarEvaluation :
    BalancedTensor.obj A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
      (ScalarExtension.rightModule φ (EndomorphismObject E) (endomorphismHomRight A D E Y))
      (ScalarExtension.leftModule φ (EndomorphismObject E) (endomorphismHomLeft A D E X)) ⟶
        (ScalarExtension.extension φ).obj (homObject A D X Y) :=
  (ScalarExtension.balancedIso φ (EndomorphismObject E)
    (endomorphismHomRight A D E Y) (endomorphismHomLeft A D E X)).inv ≫
      (ScalarExtension.extension φ).map (endomorphismEvaluation A D E X Y)

lemma endomorphismScalarEvaluation_ι (b : EndomorphismObject E) :
    BalancedTensor.ι A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
        (ScalarExtension.rightModule φ (EndomorphismObject E) (endomorphismHomRight A D E Y))
        (ScalarExtension.leftModule φ (EndomorphismObject E) (endomorphismHomLeft A D E X)) b ≫
      endomorphismScalarEvaluation φ D E X Y =
    (ScalarExtension.tensorIso φ (homObject A D E Y) (homObject A D X E)).inv ≫
      (ScalarExtension.extension φ).map (endomorphismEvaluationComponent A D E X Y) := by
  unfold endomorphismScalarEvaluation
  rw [ScalarExtension.balancedIso_inv_ι_assoc, ← CategoryTheory.Functor.map_comp,
    endomorphismEvaluation_ι]
  rfl

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

/-- 任意の環準同型で、導来係数変更の比較射とbalanced合成評価は可換する。 -/
lemma endomorphismDerivedScalarEvaluation_square :
    ScalarExtension.derivedBalancedComparison φ (EndomorphismObject E)
        (endomorphismHomRight A D E Y) (endomorphismHomLeft A D E X) ≫
      DerivedCategory.Q.map (endomorphismScalarEvaluation φ D E X Y) =
    (ScalarExtension.complexDerivedExtension φ).map
        (DerivedCategory.Q.map (endomorphismEvaluation A D E X Y)) ≫
      (ScalarExtension.complexDerivedExtensionAugmentation φ).app (homObject A D X Y) := by
  unfold ScalarExtension.derivedBalancedComparison endomorphismScalarEvaluation
  rw [CategoryTheory.Functor.map_comp, Category.assoc,
    ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact ((ScalarExtension.complexDerivedExtensionAugmentation φ).naturality
    (endomorphismEvaluation A D E X Y)).symm

end SerrePositivity.DifferentialGraded
end

end ScalarEvaluation

/-! ## ScalarHomFactors（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarHomFactors.lean） -/

/-! # 係数変更したHom因子と実際の係数変更dg圏のHomの比較 -/

@[expose] public section ScalarHomFactors

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end ScalarHomFactors

/-! ## ScalarEvaluationActual（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarEvaluationActual.lean） -/

/-! # 実際の係数変更先Hom因子との合成評価の可換性 -/

@[expose] public section ScalarEvaluationActual

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] (E X Y : D)

lemma endomorphismEvaluationComponentScalar :
    (ScalarExtension.tensorIso φ (homObject A D E Y) (homObject A D X E)).inv ≫
        (ScalarExtension.extension φ).map (endomorphismEvaluationComponent A D E X Y) =
      endomorphismEvaluationComponent A' (ScalarExtension.DGBaseChange φ D) E X Y := by
  unfold endomorphismEvaluationComponent
  rw [CategoryTheory.Functor.map_comp]
  change _ = (β_ ((ScalarExtension.extension φ).obj (homObject A D E Y))
    ((ScalarExtension.extension φ).obj (homObject A D X E))).hom ≫
      (ScalarExtension.tensorIso φ (homObject A D X E) (homObject A D E Y)).inv ≫
        (ScalarExtension.extension φ).map (eComp (Complex A) X E Y)
  rw [ScalarExtension.tensorIso_braiding_assoc]
  rfl

lemma endomorphismScalarHomTensorIso_evaluation :
    (endomorphismScalarHomTensorIso φ D E X Y).hom ≫
        endomorphismEvaluation A' (ScalarExtension.DGBaseChange φ D) E X Y =
      endomorphismScalarEvaluation φ D E X Y := by
  apply BalancedTensor.hom_ext A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
  intro b
  rw [← Category.assoc, endomorphismScalarHomTensorIso_ι,
    endomorphismEvaluation_ι, endomorphismScalarEvaluation_ι,
    endomorphismEvaluationComponentScalar]

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

/-- 先に構成した比較射を、実際の係数変更先dg圏の合成評価へ接続する。 -/
lemma endomorphismDerivedScalarActualEvaluation_square :
    ScalarExtension.derivedBalancedComparison φ (EndomorphismObject E)
        (endomorphismHomRight A D E Y) (endomorphismHomLeft A D E X) ≫
      DerivedCategory.Q.map (endomorphismScalarHomTensorIso φ D E X Y).hom ≫
      DerivedCategory.Q.map
        (endomorphismEvaluation A' (ScalarExtension.DGBaseChange φ D) E X Y) =
    (ScalarExtension.complexDerivedExtension φ).map
        (DerivedCategory.Q.map (endomorphismEvaluation A D E X Y)) ≫
      (ScalarExtension.complexDerivedExtensionAugmentation φ).app (homObject A D X Y) := by
  rw [← CategoryTheory.Functor.map_comp, endomorphismScalarHomTensorIso_evaluation]
  exact endomorphismDerivedScalarEvaluation_square φ D E X Y

end SerrePositivity.DifferentialGraded
end

end ScalarEvaluationActual

/-! ## ScalarRepresentable（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarRepresentable.lean） -/

/-! # 実際の代表加群と係数変更の一致 -/

@[expose] public section ScalarRepresentable

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] (z : D)

lemma scalarRepresentable_eq :
    ScalarExtension.rightModule φ D (representable A z) =
      representable A' (show ScalarExtension.DGBaseChange φ D from z) := by
  let := φ.toAlgebra
  apply EnrichedFunctor.ext (Complex A')
    (F := (ScalarExtension.rightModule φ D (representable A z)).toFunctor)
    (G := (representable A' (show ScalarExtension.DGBaseChange φ D from z)).toFunctor)
    (fun _ => rfl)
  intro x y
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
  change ((ScalarExtension.homComparison φ _ _).f p
    ((ModuleCat.extendScalars φ).map (((representable A z).map x y).f p)
      ((1 : A') ⊗ₜ[A] f))).v r n hn ((1 : A') ⊗ₜ[A] m) = _
  erw [ModuleCat.ExtendScalars.map_tmul φ, ScalarExtension.homComparison_apply]
  change (1 : A') ⊗ₜ[A] forward A (D := D) f m (by omega) =
    forward A' (D := ScalarExtension.DGBaseChange φ D)
      ((1 : A') ⊗ₜ[A] f) ((1 : A') ⊗ₜ[A] m) (by omega)
  exact (endomorphismScalarForward_one φ D f m (by omega)).symm

end SerrePositivity.DifferentialGraded
end

end ScalarRepresentable

/-! ## ScalarModuleHomNaturality（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarModuleHomNaturality.lean） -/

/-! # 実際の係数変更加群間のHomへ向かう全次数自然性 -/

@[expose] public section ScalarModuleHomNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
@[reassoc]
lemma scalarTensorIso_inv_naturality {K K' L L' : Complex A} (f : K ⟶ K') (g : L ⟶ L') :
    ((ScalarExtension.extension φ).map f ⊗ₘ (ScalarExtension.extension φ).map g) ≫
        (ScalarExtension.tensorIso φ K' L').inv =
      (ScalarExtension.tensorIso φ K L).inv ≫ (ScalarExtension.extension φ).map (f ⊗ₘ g) := by
  apply (cancel_epi (ScalarExtension.tensorIso φ K L).hom).1
  rw [Iso.hom_inv_id_assoc, ← ScalarExtension.tensorIso_naturality_assoc,
    Iso.hom_inv_id, Category.comp_id]

variable (D : Type v) [DGCategory A D]

/-- パラメータ付き自然変換の各成分を、実際に係数変更した加群の間へ送る。 -/
lemma scalarModuleParamNaturality {M N : RightModule A D} {K : Complex A}
    (a : ModuleParamTrans A D K M N) (x y : Dᵒᵖ) :
    (β_ ((ScalarExtension.extension φ).obj K)
      ((ScalarExtension.extension φ).obj (x ⟶[Complex A] y))).hom ≫
      ((ScalarExtension.rightModule φ D M).map x y ⊗ₘ
        ((ScalarExtension.extension φ).map (a.app y) ≫
          ScalarExtension.homComparison φ (M.obj y) (N.obj y))) ≫
        enrichedComposition _ _ _ =
    (((ScalarExtension.extension φ).map (a.app x) ≫
        ScalarExtension.homComparison φ (M.obj x) (N.obj x)) ⊗ₘ
      (ScalarExtension.rightModule φ D N).map x y) ≫ enrichedComposition _ _ _ := by
  rw [ScalarExtension.rightModule_map, ScalarExtension.rightModule_map]
  change (β_ ((ScalarExtension.extension φ).obj K)
      ((ScalarExtension.extension φ).obj (x ⟶[Complex A] y))).hom ≫
    (((ScalarExtension.extension φ).map (M.map x y) ≫ ScalarExtension.homComparison φ _ _) ⊗ₘ
      ((ScalarExtension.extension φ).map (a.app y) ≫ ScalarExtension.homComparison φ _ _)) ≫
        enrichedComposition ((ScalarExtension.extension φ).obj (M.obj x))
          ((ScalarExtension.extension φ).obj (M.obj y))
          ((ScalarExtension.extension φ).obj (N.obj y)) =
    (((ScalarExtension.extension φ).map (a.app x) ≫ ScalarExtension.homComparison φ _ _) ⊗ₘ
      ((ScalarExtension.extension φ).map (N.map x y) ≫ ScalarExtension.homComparison φ _ _)) ≫
        enrichedComposition ((ScalarExtension.extension φ).obj (M.obj x))
          ((ScalarExtension.extension φ).obj (N.obj x))
          ((ScalarExtension.extension φ).obj (N.obj y))
  simp only [← tensorHom_comp_tensorHom, Category.assoc]
  rw [← ScalarExtension.homComparison_composition,
    ← ScalarExtension.homComparison_composition]
  erw [scalarTensorIso_inv_naturality_assoc φ (M.map x y) (a.app y),
    scalarTensorIso_inv_naturality_assoc φ (a.app x) (N.map x y)]
  erw [ScalarExtension.tensorIso_braiding_assoc φ K (x ⟶[Complex A] y)]
  change (ScalarExtension.tensorIso φ K (x ⟶[Complex A] y)).inv ≫
      (ScalarExtension.extension φ).map (β_ K (x ⟶[Complex A] y)).hom ≫
      (ScalarExtension.extension φ).map (M.map x y ⊗ₘ a.app y) ≫
      (ScalarExtension.extension φ).map (enrichedComposition (M.obj x) (M.obj y) (N.obj y)) ≫
      ScalarExtension.homComparison φ (M.obj x) (N.obj y) =
    (ScalarExtension.tensorIso φ K (x ⟶[Complex A] y)).inv ≫
      (ScalarExtension.extension φ).map (a.app x ⊗ₘ N.map x y) ≫
      (ScalarExtension.extension φ).map (enrichedComposition (M.obj x) (N.obj x) (N.obj y)) ≫
      ScalarExtension.homComparison φ (M.obj x) (N.obj y)
  simp only [← CategoryTheory.Functor.map_comp_assoc]
  exact congrArg (fun f => (ScalarExtension.tensorIso φ K (x ⟶[Complex A] y)).inv ≫
    (ScalarExtension.extension φ).map f ≫
      ScalarExtension.homComparison φ (M.obj x) (N.obj y)) (a.naturality x y)

end SerrePositivity.DifferentialGraded
end

end ScalarModuleHomNaturality

/-! ## ScalarModuleHom（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarModuleHom.lean） -/

/-! # 係数変更した実際の加群間の全次数Hom比較

Hom endの係数変更から実際の係数変更加群間のHom endへの射を構成する。
有限性やflat性を仮定せず、この射の可逆性は主張しない。
-/

@[expose] public section ScalarModuleHom

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D]

def scalarModuleParamTrans {M N : RightModule A D} {K : Complex A}
    (a : ModuleParamTrans A D K M N) :
    ModuleParamTrans A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.extension φ).obj K)
      (ScalarExtension.rightModule φ D M) (ScalarExtension.rightModule φ D N) where
  app x := (ScalarExtension.extension φ).map (a.app x) ≫
    ScalarExtension.homComparison φ (M.obj x) (N.obj x)
  naturality x y := scalarModuleParamNaturality φ D a x y

variable [Small.{u} D]

def scalarModuleHom (M N : RightModule A D) :
    (ScalarExtension.extension φ).obj (moduleHom A D M N) ⟶
      moduleHom A' (ScalarExtension.DGBaseChange φ D)
        (ScalarExtension.rightModule φ D M) (ScalarExtension.rightModule φ D N) :=
  (moduleHomEquiv A' (ScalarExtension.DGBaseChange φ D) _ _ _).symm
    (scalarModuleParamTrans φ D
      ((moduleHomEquiv A D (moduleHom A D M N) M N) (𝟙 _)))

@[reassoc]
lemma scalarModuleHom_π (M N : RightModule A D) (x : D) :
    scalarModuleHom φ D M N ≫
        moduleHomπ A' (ScalarExtension.DGBaseChange φ D)
          (ScalarExtension.rightModule φ D M) (ScalarExtension.rightModule φ D N) x =
      (ScalarExtension.extension φ).map (moduleHomπ A D M N x) ≫
        ScalarExtension.homComparison φ (M.obj (op x)) (N.obj (op x)) := by
  rw [scalarModuleHom, moduleHomEquiv_symm_π]
  change (ScalarExtension.extension φ).map (𝟙 _ ≫ moduleHomπ A D M N x) ≫ _ = _
  rw [Category.id_comp]

end SerrePositivity.DifferentialGraded
end

end ScalarModuleHom

/-! ## ScalarModuleDGFunctor（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarModuleDGFunctor.lean） -/

/-! # 実際の係数変更加群圏へ向かうdg関手 -/

@[expose] public section ScalarModuleDGFunctor

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleHom_identity (M : RightModule A D) :
    (ScalarExtension.unitIso φ).inv ≫
        (ScalarExtension.extension φ).map (moduleIdentity A D M) ≫ scalarModuleHom φ D M M =
      moduleIdentity A' (ScalarExtension.DGBaseChange φ D) (ScalarExtension.rightModule φ D M) := by
  apply moduleHom_ext
  intro x
  rw [Category.assoc, Category.assoc, scalarModuleHom_π,
    ← CategoryTheory.Functor.map_comp_assoc, moduleIdentity_π, moduleIdentity_π]
  exact ScalarExtension.homComparison_identity φ (M.obj (Opposite.op x))

lemma scalarModuleHom_composition (M N P : RightModule A D) :
    (ScalarExtension.tensorIso φ (moduleHom A D M N) (moduleHom A D N P)).inv ≫
        (ScalarExtension.extension φ).map (moduleComposition A D M N P) ≫
          scalarModuleHom φ D M P =
      (scalarModuleHom φ D M N ⊗ₘ scalarModuleHom φ D N P) ≫
        moduleComposition A' (ScalarExtension.DGBaseChange φ D)
          (ScalarExtension.rightModule φ D M) (ScalarExtension.rightModule φ D N)
          (ScalarExtension.rightModule φ D P) := by
  apply moduleHom_ext
  intro x
  simp only [Category.assoc, scalarModuleHom_π, moduleComposition_π]
  rw [tensorHom_comp_tensorHom_assoc, scalarModuleHom_π, scalarModuleHom_π,
    ← tensorHom_comp_tensorHom_assoc]
  erw [← ScalarExtension.homComparison_composition φ (M.obj (Opposite.op x))
    (N.obj (Opposite.op x)) (P.obj (Opposite.op x))]
  rw [scalarTensorIso_inv_naturality_assoc,
    ← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    moduleComposition_π]

/-- 移送したambient enrichmentから、実際のD係数変更加群圏への比較。 -/
def scalarModuleDGFunctor :
    DGFunctor A' (ScalarExtension.DGBaseChange φ (RightModule A D))
      (RightModule A' (ScalarExtension.DGBaseChange φ D)) where
  obj := ScalarExtension.rightModule φ D
  map M N := scalarModuleHom φ D M N
  map_id M := scalarModuleHom_identity φ D M
  map_comp M N P := scalarModuleHom_composition φ D M N P

end SerrePositivity.DifferentialGraded
end

end ScalarModuleDGFunctor

/-! ## ScalarYonedaHom（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarYonedaHom.lean） -/

/-! # 実際の加群Hom係数変更比較とdg Yoneda評価 -/

@[expose] public section ScalarYonedaHom

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] (z : D)

lemma scalarUnitElement_one :
    let := φ.toAlgebra
    (unitElement A' (show ScalarExtension.DGBaseChange φ D from z)).val =
      (1 : A') ⊗ₜ[A] (unitElement A z).val := by
  let := φ.toAlgebra
  change ((ScalarExtension.extension φ).map (eId (Complex A) z)).f 0
    ((ScalarExtension.unitIso φ).inv.f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A'))).inv (1 : A'))) = _
  erw [ScalarExtension.sphereIso_inv_one φ 0, ModuleCat.ExtendScalars.map_tmul φ]
  rfl

variable [Small.{u} D] (M : RightModule A D)

def scalarModuleYonedaEvaluation :
    moduleHom A' (ScalarExtension.DGBaseChange φ D)
        (ScalarExtension.rightModule φ D (representable A z)) (ScalarExtension.rightModule φ D M) ⟶
      (ScalarExtension.extension φ).obj (M.obj (op z)) :=
  yonedaEvaluateFamily A' (show ScalarExtension.DGBaseChange φ D from z)
    (ScalarExtension.rightModule φ D M)
    (fun y => moduleHomπ A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D (representable A z))
      (ScalarExtension.rightModule φ D M) y.unop)

/-- 実際の加群Hom係数変更比較は、dg Yonedaの単位評価と可換する。 -/
lemma scalarModuleHom_yoneda_square :
    scalarModuleHom φ D (representable A z) M ≫ scalarModuleYonedaEvaluation φ D z M =
      (ScalarExtension.extension φ).map (dgYonedaIso A z M).hom := by
  let := φ.toAlgebra
  apply HomologicalComplex.hom_ext
  intro p
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  change (scalarModuleYonedaEvaluation φ D z M).f p
    ((scalarModuleHom φ D (representable A z) M).f p ((1 : A') ⊗ₜ[A] t)) = _
  refine (yonedaEvaluateFamily_apply A' (show ScalarExtension.DGBaseChange φ D from z)
    (ScalarExtension.rightModule φ D M)
    (fun y => moduleHomπ A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D (representable A z))
      (ScalarExtension.rightModule φ D M) y.unop) p
    ((scalarModuleHom φ D (representable A z) M).f p ((1 : A') ⊗ₜ[A] t))).trans ?_
  have hπ := congrArg (fun f => f.f p ((1 : A') ⊗ₜ[A] t))
    (scalarModuleHom_π φ D (representable A z) M z)
  change (moduleHomπ A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D (representable A z))
      (ScalarExtension.rightModule φ D M) z).f p
      ((scalarModuleHom φ D (representable A z) M).f p ((1 : A') ⊗ₜ[A] t)) = _ at hπ
  change ((moduleHomπ A' (ScalarExtension.DGBaseChange φ D)
    (ScalarExtension.rightModule φ D (representable A z))
      (ScalarExtension.rightModule φ D M) z).f p
      ((scalarModuleHom φ D (representable A z) M).f p ((1 : A') ⊗ₜ[A] t))).v 0 p (by omega)
      (unitElement A' (show ScalarExtension.DGBaseChange φ D from z)).val =
    ((ScalarExtension.extension φ).map (dgYonedaIso A z M).hom).f p ((1 : A') ⊗ₜ[A] t)
  rw [hπ, scalarUnitElement_one φ D z]
  erw [ModuleCat.ExtendScalars.map_tmul φ, ScalarExtension.homComparison_apply]
  exact congrArg (fun m => (1 : A') ⊗ₜ[A] m)
    (yonedaEvaluateFamily_apply A z M
      (fun y => moduleHomπ A D (representable A z) M y.unop) p t).symm

end SerrePositivity.DifferentialGraded
end

end ScalarYonedaHom

/-! ## ScalarYonedaIso（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarYonedaIso.lean） -/

/-! # 代表加群を始域とする実際のHom係数変更比較の可逆性 -/

@[expose] public section ScalarYonedaIso

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite

def moduleHomEvaluateAt (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
    [Small.{u} D] (B M : RightModule A D) (z : D) (η : 𝟙_ (Complex A) ⟶ B.obj (op z)) :
    moduleHom A D B M ⟶ M.obj (op z) :=
  (ρ_ _).inv ≫ (𝟙 _ ⊗ₘ η) ≫ uncurryRight (moduleHomπ A D B M z)

lemma moduleHomEvaluateAt_eqToIso (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
    [Small.{u} D] (B M : RightModule A D) (z : D) (h : B = representable A z) :
    (eqToIso (congrArg (fun N => moduleHom A D N M) h)).hom ≫ (dgYonedaIso A z M).hom =
      moduleHomEvaluateAt A D B M z
        (eId (Complex A) z ≫
          eqToHom (congrArg (fun N : RightModule A D => N.obj (op z)) h.symm)) := by
  subst B
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp, eqToHom_refl, Category.comp_id]
  rfl

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D] (z : D) (M : RightModule A D)

lemma scalarModuleYonedaEvaluation_isIso : IsIso (scalarModuleYonedaEvaluation φ D z M) := by
  let e := eqToIso (congrArg (fun N => moduleHom A' (ScalarExtension.DGBaseChange φ D)
    N (ScalarExtension.rightModule φ D M)) (scalarRepresentable_eq φ D z)) ≪≫
      dgYonedaIso A' (show ScalarExtension.DGBaseChange φ D from z)
        (ScalarExtension.rightModule φ D M)
  have he := moduleHomEvaluateAt_eqToIso A' (ScalarExtension.DGBaseChange φ D)
    (ScalarExtension.rightModule φ D (representable A z)) (ScalarExtension.rightModule φ D M)
    z (scalarRepresentable_eq φ D z)
  have he' : e.hom = scalarModuleYonedaEvaluation φ D z M := by
    change _ = moduleHomEvaluateAt A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D (representable A z)) (ScalarExtension.rightModule φ D M)
      z (eId (Complex A') (show ScalarExtension.DGBaseChange φ D from z))
    exact he
  rw [← he']
  infer_instance

/-- 代表加群を始域とする実際のHom比較は、任意の係数環準同型に対して可逆。 -/
lemma scalarModuleHom_representable_isIso :
    IsIso (scalarModuleHom φ D (representable A z) M) := by
  let := scalarModuleYonedaEvaluation_isIso φ D z M
  have : IsIso (scalarModuleHom φ D (representable A z) M ≫
      scalarModuleYonedaEvaluation φ D z M) := by
    rw [scalarModuleHom_yoneda_square]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (scalarModuleYonedaEvaluation φ D z M)

end SerrePositivity.DifferentialGraded
end

end ScalarYonedaIso

/-! ## ScalarClosedMap（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarClosedMap.lean） -/

/-! # 実際のHom係数変更比較と閉零加群射の一致 -/

@[expose] public section ScalarClosedMap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

lemma scalarHomComparison_closedMap {K L : Complex A} (f : K ⟶ L) :
    (ScalarExtension.unitIso φ).inv ≫ (ScalarExtension.extension φ).map (closedMap A f) ≫
        ScalarExtension.homComparison φ K L =
      closedMap A' ((ScalarExtension.extension φ).map f) := by
  let := φ.toAlgebra
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (ScalarExtension.homComparison φ K L).f 0
    (((ScalarExtension.extension φ).map (closedMap A f)).f 0
      ((ScalarExtension.unitIso φ).inv.f 0
        ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A'))).inv (1 : A')))) = _
  erw [ScalarExtension.sphereIso_inv_one φ 0, ModuleCat.ExtendScalars.map_tmul φ]
  have hc : (closedMap A f).f 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) = Cochain.ofHom f :=
    closedMap_cycle A f
  rw [hc]
  change (ScalarExtension.homComparison φ K L).f 0 ((1 : A') ⊗ₜ[A] Cochain.ofHom f) =
    (cycleFromUnit _ (closedMap A' ((ScalarExtension.extension φ).map f))).val
  rw [closedMap_cycle]
  apply Cochain.ext₀
  intro i
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((ScalarExtension.homComparison φ K L).f 0 ((1 : A') ⊗ₜ[A] Cochain.ofHom f)).v
      i i (add_zero i) ((1 : A') ⊗ₜ[A] x) =
    ((ScalarExtension.extension φ).map f).f i ((1 : A') ⊗ₜ[A] x)
  erw [ScalarExtension.homComparison_apply φ K L 0 i i (add_zero i)]
  rfl

variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleHom_closedMap {M N : ModuleCategory A D} (f : M ⟶ N) :
    (ScalarExtension.unitIso φ).inv ≫
        (ScalarExtension.extension φ).map (ForgetEnrichment.homTo (Complex A) f) ≫
        scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
          (ForgetEnrichment.to (Complex A) N) =
      ForgetEnrichment.homTo (Complex A') ((ScalarExtension.moduleExtension φ D).map f) := by
  apply moduleHom_ext
  intro x
  rw [Category.assoc, Category.assoc, scalarModuleHom_π,
    ← CategoryTheory.Functor.map_comp_assoc, ← moduleEvaluation_closedMap]
  have hx := moduleEvaluation_closedMap A' (ScalarExtension.DGBaseChange φ D) x
    ((ScalarExtension.moduleExtension φ D).map f)
  rw [ScalarExtension.moduleExtension_eval] at hx
  exact (scalarHomComparison_closedMap φ ((moduleEvaluation A D x).map f)).trans hx

end SerrePositivity.DifferentialGraded
end

end ScalarClosedMap

/-! ## ScalarHomNaturality（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarHomNaturality.lean） -/

/-! # 実際のHom係数変更比較の閉零射に関する両変数自然性 -/

@[expose] public section ScalarHomNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleHom_precompose {M N : ModuleCategory A D} (f : M ⟶ N)
    (P : ModuleCategory A D) :
    (ScalarExtension.extension φ).map (eHomWhiskerRight (Complex A) f P) ≫
        scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
          (ForgetEnrichment.to (Complex A) P) =
      scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) P) ≫
        eHomWhiskerRight (Complex A') ((ScalarExtension.moduleExtension φ D).map f)
          ((ScalarExtension.moduleExtension φ D).obj P) := by
  apply moduleHom_ext
  intro x
  let L := ScalarExtension.extension φ
  let F := ScalarExtension.moduleExtension φ D
  let π := moduleHomπ A D
  let c := ScalarExtension.homComparison φ
  let s (X Y : ModuleCategory A D) := scalarModuleHom φ D
    (ForgetEnrichment.to (Complex A) X) (ForgetEnrichment.to (Complex A) Y)
  have hr := moduleHomWhiskerRight_π A' (ScalarExtension.DGBaseChange φ D)
    (P := F.obj P) (F.map f) x
  rw [ScalarExtension.moduleExtension_eval] at hr
  have hπM := scalarModuleHom_π φ D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) P) x
  have hπN := scalarModuleHom_π φ D (ForgetEnrichment.to (Complex A) N)
    (ForgetEnrichment.to (Complex A) P) x
  calc
    _ = L.map (eHomWhiskerRight (Complex A) f P) ≫
        (L.map (π (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) P) x) ≫
          c ((moduleEvaluation A D x).obj M) ((moduleEvaluation A D x).obj P)) := by
      rw [Category.assoc]
      exact congrArg (fun k => L.map (eHomWhiskerRight (Complex A) f P) ≫ k) hπM
    _ = L.map (π (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) P) x) ≫
        c ((moduleEvaluation A D x).obj N) ((moduleEvaluation A D x).obj P) ≫
          homPrecompose (L.map ((moduleEvaluation A D x).map f))
            (L.obj ((moduleEvaluation A D x).obj P)) := by
      rw [← CategoryTheory.Functor.map_comp_assoc, moduleHomWhiskerRight_π,
        CategoryTheory.Functor.map_comp, Category.assoc]
      exact congrArg (fun k => L.map (π (ForgetEnrichment.to (Complex A) N)
        (ForgetEnrichment.to (Complex A) P) x) ≫ k)
        (ScalarExtension.homComparison_precompose φ ((moduleEvaluation A D x).map f) _)
    _ = _ := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ homPrecompose (L.map ((moduleEvaluation A D x).map f))
          (L.obj ((moduleEvaluation A D x).obj P))) hπN.symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun k => s N P ≫ k) hr.symm).trans (Category.assoc _ _ _).symm)))

lemma scalarModuleHom_postcompose (M : ModuleCategory A D) {N P : ModuleCategory A D}
    (f : N ⟶ P) :
    (ScalarExtension.extension φ).map (eHomWhiskerLeft (Complex A) M f) ≫
        scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
          (ForgetEnrichment.to (Complex A) P) =
      scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) ≫
        eHomWhiskerLeft (Complex A') ((ScalarExtension.moduleExtension φ D).obj M)
          ((ScalarExtension.moduleExtension φ D).map f) := by
  apply moduleHom_ext
  intro x
  let L := ScalarExtension.extension φ
  let F := ScalarExtension.moduleExtension φ D
  let π := moduleHomπ A D
  let c := ScalarExtension.homComparison φ
  let s (X Y : ModuleCategory A D) := scalarModuleHom φ D
    (ForgetEnrichment.to (Complex A) X) (ForgetEnrichment.to (Complex A) Y)
  have hr := moduleHomWhiskerLeft_π A' (ScalarExtension.DGBaseChange φ D)
    (M := F.obj M) (F.map f) x
  rw [ScalarExtension.moduleExtension_eval] at hr
  have hπP := scalarModuleHom_π φ D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) P) x
  have hπN := scalarModuleHom_π φ D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N) x
  calc
    _ = L.map (eHomWhiskerLeft (Complex A) M f) ≫
        (L.map (π (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) P) x) ≫
          c ((moduleEvaluation A D x).obj M) ((moduleEvaluation A D x).obj P)) := by
      rw [Category.assoc]
      exact congrArg (fun k => L.map (eHomWhiskerLeft (Complex A) M f) ≫ k) hπP
    _ = L.map (π (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) x) ≫
        c ((moduleEvaluation A D x).obj M) ((moduleEvaluation A D x).obj N) ≫
          homPostcompose (L.obj ((moduleEvaluation A D x).obj M))
            (L.map ((moduleEvaluation A D x).map f)) := by
      rw [← CategoryTheory.Functor.map_comp_assoc, moduleHomWhiskerLeft_π,
        CategoryTheory.Functor.map_comp, Category.assoc]
      exact congrArg (fun k => L.map (π (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) N) x) ≫ k)
        (ScalarExtension.homComparison_postcompose φ _ ((moduleEvaluation A D x).map f))
    _ = _ := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ homPostcompose (L.obj ((moduleEvaluation A D x).obj M))
          (L.map ((moduleEvaluation A D x).map f))) hπN.symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun k => s M N ≫ k) hr.symm).trans (Category.assoc _ _ _).symm)))

end SerrePositivity.DifferentialGraded
end

end ScalarHomNaturality

/-! ## ScalarHomRetracts（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarHomRetracts.lean） -/

/-! # 実際のHom係数変更比較と始域のretract -/

@[expose] public section ScalarHomRetracts

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

def scalarModuleHom_retractArrow {M N : ModuleCategory A D} (r : Retract M N)
    (P : ModuleCategory A D) :
    RetractArrow
      (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) P))
      (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N)
        (ForgetEnrichment.to (Complex A) P)) where
  i := Arrow.homMk
    ((ScalarExtension.extension φ).map (eHomWhiskerRight (Complex A) r.r P))
    (eHomWhiskerRight (Complex A') ((ScalarExtension.moduleExtension φ D).map r.r)
      ((ScalarExtension.moduleExtension φ D).obj P))
    (scalarModuleHom_precompose φ D r.r P)
  r := Arrow.homMk
    ((ScalarExtension.extension φ).map (eHomWhiskerRight (Complex A) r.i P))
    (eHomWhiskerRight (Complex A') ((ScalarExtension.moduleExtension φ D).map r.i)
      ((ScalarExtension.moduleExtension φ D).obj P))
    (scalarModuleHom_precompose φ D r.i P)
  retract := by
    apply Arrow.hom_ext
    · change (ScalarExtension.extension φ).map (eHomWhiskerRight (Complex A) r.r P) ≫
        (ScalarExtension.extension φ).map (eHomWhiskerRight (Complex A) r.i P) = 𝟙 _
      rw [← CategoryTheory.Functor.map_comp, ← eHomWhiskerRight_comp, r.retract,
        eHomWhiskerRight_id, CategoryTheory.Functor.map_id]
    · change eHomWhiskerRight (Complex A') ((ScalarExtension.moduleExtension φ D).map r.r)
          ((ScalarExtension.moduleExtension φ D).obj P) ≫
        eHomWhiskerRight (Complex A') ((ScalarExtension.moduleExtension φ D).map r.i)
          ((ScalarExtension.moduleExtension φ D).obj P) = 𝟙 _
      rw [← eHomWhiskerRight_comp, ← CategoryTheory.Functor.map_comp, r.retract,
        CategoryTheory.Functor.map_id, eHomWhiskerRight_id]

lemma scalarModuleHom_isIso_of_retract {M N : ModuleCategory A D} (r : Retract M N)
    (P : ModuleCategory A D)
    (hN : IsIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) P))) :
    IsIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) P)) :=
  MorphismProperty.of_retract (P := MorphismProperty.isomorphisms (Complex A'))
    (scalarModuleHom_retractArrow φ D r P) hN

lemma scalarModuleHom_quasiIso_of_retract {M N : ModuleCategory A D} (r : Retract M N)
    (P : ModuleCategory A D)
    (hN : QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) P))) :
    QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) P)) :=
  MorphismProperty.of_retract (P := HomologicalComplex.quasiIso (ModuleCat A') (.up ℤ))
    (scalarModuleHom_retractArrow φ D r P) hN

end SerrePositivity.DifferentialGraded
end

end ScalarHomRetracts

/-! ## ScalarModuleHomotopy（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarModuleHomotopy.lean） -/

/-! # 実際の係数拡大による全dg自然な加群ホモトピーの保存 -/

@[expose] public section ScalarModuleHomotopy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleHom_cycle {M N : ModuleCategory A D} (f : M ⟶ N) :
    let := φ.toAlgebra
    (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)).f 0
        ((1 : A') ⊗ₜ[A] (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val) =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A')
        ((ScalarExtension.moduleExtension φ D).map f))).val := by
  let := φ.toAlgebra
  have h := congrArg (fun k => (cycleFromUnit _ k).val) (scalarModuleHom_closedMap φ D f)
  change (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)).f 0
    (((ScalarExtension.extension φ).map (ForgetEnrichment.homTo (Complex A) f)).f 0
      ((ScalarExtension.unitIso φ).inv.f 0
        ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A'))).inv (1 : A')))) = _ at h
  erw [ScalarExtension.sphereIso_inv_one φ 0, ModuleCat.ExtendScalars.map_tmul φ] at h
  exact h

/-- 次数−1のHom end要素を係数変更する。各値だけのホモトピーには弱めない。 -/
def scalarModuleHomotopy {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ModuleHomotopy A D f g) :
    ModuleHomotopy A' (ScalarExtension.DGBaseChange φ D)
      ((ScalarExtension.moduleExtension φ D).map f)
      ((ScalarExtension.moduleExtension φ D).map g) := by
  let := φ.toAlgebra
  let s := scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N)
  refine ⟨s.f (-1) ((1 : A') ⊗ₜ[A] h.val), ?_⟩
  have hc := congrArg (fun k => k ((1 : A') ⊗ₜ[A] h.val)) (s.comm (-1) 0)
  change _ = s.f 0 ((ModuleCat.extendScalars φ).map
    ((homObject A (RightModule A D) M N).d (-1) 0) ((1 : A') ⊗ₜ[A] h.val)) at hc
  erw [ModuleCat.ExtendScalars.map_tmul φ] at hc
  change (moduleHom A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D (ForgetEnrichment.to (Complex A) M))
      (ScalarExtension.rightModule φ D (ForgetEnrichment.to (Complex A) N))).d (-1) 0
      (s.f (-1) ((1 : A') ⊗ₜ[A] h.val)) = _ at hc
  calc
    _ = s.f 0 ((1 : A') ⊗ₜ[A]
        ((homObject A (RightModule A D) M N).d (-1) 0 h.val)) := hc
    _ = _ := by
      rw [h.property, TensorProduct.tmul_sub, map_sub]
      exact congrArg₂ (fun a b => a - b) (scalarModuleHom_cycle φ D f)
        (scalarModuleHom_cycle φ D g)

/-- 実際の加群係数拡大を全dg自然なホモトピーの商へ降ろす。 -/
def scalarModuleExtensionHomotopy : ModuleHomotopyCategory A D ⥤
    ModuleHomotopyCategory A' (ScalarExtension.DGBaseChange φ D) :=
  CategoryTheory.Quotient.lift _ (ScalarExtension.moduleExtension φ D ⋙
    moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D)) (by
      intro M N f g hb
      obtain ⟨h⟩ := (moduleHomotopy_nonempty_iff A D f g).2 hb
      exact (moduleToHomotopy_map_eq_iff A' (ScalarExtension.DGBaseChange φ D) _ _).2
        ⟨scalarModuleHomotopy φ D h⟩)

lemma scalarModuleExtensionHomotopy_fac :
    moduleToHomotopy A D ⋙ scalarModuleExtensionHomotopy φ D =
      ScalarExtension.moduleExtension φ D ⋙
        moduleToHomotopy A' (ScalarExtension.DGBaseChange φ D) :=
  CategoryTheory.Quotient.lift_spec _ _ _

end SerrePositivity.DifferentialGraded
end

end ScalarModuleHomotopy

/-! ## ScalarHomElements（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarHomElements.lean） -/

/-! # 実際の加群係数拡大による全次数Hom要素の合成保存 -/

@[expose] public section ScalarHomElements

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

lemma scalarBaseChange_forward {D : Type v} [DGCategory A D]
    {x y z : D} {p q n : ℤ} (f : GradedHom A x y p) (g : GradedHom A y z q)
    (h : p + q = n) :
    let := φ.toAlgebra
    forward A' (D := ScalarExtension.DGBaseChange φ D)
      (x := x) (y := y) (z := z) ((1 : A') ⊗ₜ[A] f) ((1 : A') ⊗ₜ[A] g) h =
      (1 : A') ⊗ₜ[A] forward A f g h := by
  let := φ.toAlgebra
  change ((ScalarExtension.extension φ).map (eComp (Complex A) x y z)).f n
    ((ScalarExtension.tensorIso φ (x ⟶[Complex A] y) (y ⟶[Complex A] z)).inv.f n
      (ιTensorObj ((ScalarExtension.extension φ).obj (x ⟶[Complex A] y))
        ((ScalarExtension.extension φ).obj (y ⟶[Complex A] z)) p q n h
        (((1 : A') ⊗ₜ[A] f) ⊗ₜ[A'] ((1 : A') ⊗ₜ[A] g)))) = _
  erw [ScalarExtension.tensorIso_inv_apply φ (x ⟶[Complex A] y) (y ⟶[Complex A] z)
    p q n h f g, ModuleCat.ExtendScalars.map_tmul φ]
  rfl

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 環を変えるHom要素写像。任意次数に定義し、閉性は要求しない。 -/
def scalarModuleHomElement {M N : RightModule A D} {p : ℤ}
    (f : GradedHom A M N p) :
    GradedHom A' (ScalarExtension.rightModule φ D M) (ScalarExtension.rightModule φ D N) p :=
  let := φ.toAlgebra
  (scalarModuleHom φ D M N).f p ((1 : A') ⊗ₜ[A] f)

lemma scalarModuleHomElement_forward {M N P : RightModule A D} {p q n : ℤ}
    (f : GradedHom A M N p) (g : GradedHom A N P q) (h : p + q = n) :
    scalarModuleHomElement φ D (forward A f g h) =
      forward A' (scalarModuleHomElement φ D f) (scalarModuleHomElement φ D g) h := by
  let := φ.toAlgebra
  have hm := (scalarModuleDGFunctor φ D).map_forward A'
    (x := (show ScalarExtension.DGBaseChange φ (RightModule A D) from M))
    (y := N) (z := P) ((1 : A') ⊗ₜ[A] f) ((1 : A') ⊗ₜ[A] g) h
  rw [scalarBaseChange_forward φ f g h] at hm
  exact hm

lemma scalarModuleHomElement_cycle {M N : ModuleCategory A D} (f : M ⟶ N) :
    scalarModuleHomElement φ D (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val =
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A')
        ((ScalarExtension.moduleExtension φ D).map f))).val :=
  scalarModuleHom_cycle φ D f

@[simp] lemma scalarModuleHomElement_zero (M N : RightModule A D) (p : ℤ) :
    scalarModuleHomElement φ D (0 : GradedHom A M N p) = 0 := by
  let := φ.toAlgebra
  simp only [scalarModuleHomElement, TensorProduct.tmul_zero, map_zero]

lemma scalarModuleHomElement_add {M N : RightModule A D} {p : ℤ}
    (f g : GradedHom A M N p) :
    scalarModuleHomElement φ D (f + g) =
      scalarModuleHomElement φ D f + scalarModuleHomElement φ D g := by
  let := φ.toAlgebra
  simp only [scalarModuleHomElement, TensorProduct.tmul_add, map_add]

lemma scalarModuleHomElement_unit (M : RightModule A D) :
    scalarModuleHomElement φ D (unitElement A M).val =
      (unitElement A' (ScalarExtension.rightModule φ D M)).val := by
  have hm := (scalarModuleDGFunctor φ D).map_unitElement A'
    (show ScalarExtension.DGBaseChange φ (RightModule A D) from M)
  rw [scalarUnitElement_one φ (RightModule A D) M] at hm
  exact hm

lemma scalarModuleHomElement_d {M N : RightModule A D} {p q : ℤ}
    (f : GradedHom A M N p) :
    (moduleHom A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D M) (ScalarExtension.rightModule φ D N)).d p q
        (scalarModuleHomElement φ D f) =
      scalarModuleHomElement φ D ((moduleHom A D M N).d p q f) := by
  let := φ.toAlgebra
  have hc := congrArg (fun k => k ((1 : A') ⊗ₜ[A] f)) ((scalarModuleHom φ D M N).comm p q)
  change _ = (scalarModuleHom φ D M N).f q
    ((ModuleCat.extendScalars φ).map ((moduleHom A D M N).d p q)
      ((1 : A') ⊗ₜ[A] f)) at hc
  erw [ModuleCat.ExtendScalars.map_tmul φ] at hc
  exact hc

end SerrePositivity.DifferentialGraded
end

end ScalarHomElements

/-! ## ScalarHomHomotopyRetracts（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarHomHomotopyRetracts.lean） -/

/-! # 実際のHom係数変更比較のH⁰内始域retract閉性 -/

@[expose] public section ScalarHomHomotopyRetracts

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleHom_quasiIso_of_homotopyRetract
    {M N : ModuleCategory A D} (i : M ⟶ N) (r : N ⟶ M)
    (h : (moduleToHomotopy A D).map (i ≫ r) = (moduleToHomotopy A D).map (𝟙 M))
    (P : ModuleCategory A D)
    (hN : QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) P))) :
    QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) P)) := by
  let L := ScalarExtension.extension φ
  let F := ScalarExtension.moduleExtension φ D
  obtain ⟨hh⟩ := (moduleToHomotopy_map_eq_iff A D _ _).mp h
  let ht := scalarModuleHomotopy φ D hh
  constructor
  intro q
  apply (quasiIsoAt_iff_isIso_homologyMap _ q).2
  have hs := ((ModuleCat.extendScalars φ).mapHomotopy
    (moduleHomPrecomposeHomotopy A D hh P)).homologyMap_eq q
  simp only [eHomWhiskerRight_comp, eHomWhiskerRight_id,
    Functor.map_comp, homologyMap_comp] at hs
  have hsId := congrArg (fun k => homologyMap k q)
    (L.map_id (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) P)))
  simp only [homologyMap_id] at hsId
  have ht' := (moduleHomPrecomposeHomotopy A' (ScalarExtension.DGBaseChange φ D)
    ht (F.obj P)).homologyMap_eq q
  simp only [Functor.map_comp, eHomWhiskerRight_comp, homologyMap_comp] at ht'
  have htId := congrArg (fun k => homologyMap
    (eHomWhiskerRight (Complex A') k (F.obj P)) q) (F.map_id M)
  simp only [eHomWhiskerRight_id, homologyMap_id] at htId
  let a : RetractArrow
      (homologyMap (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
        (ForgetEnrichment.to (Complex A) P)) q)
      (homologyMap (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N)
        (ForgetEnrichment.to (Complex A) P)) q) :=
    { i := Arrow.homMk
        (homologyMap (L.map (eHomWhiskerRight (Complex A) r P)) q)
        (homologyMap (eHomWhiskerRight (Complex A') (F.map r) (F.obj P)) q)
        (by
          have hn := congrArg (fun k => homologyMap k q) (scalarModuleHom_precompose φ D r P)
          simp only [homologyMap_comp] at hn
          exact hn)
      r := Arrow.homMk
        (homologyMap (L.map (eHomWhiskerRight (Complex A) i P)) q)
        (homologyMap (eHomWhiskerRight (Complex A') (F.map i) (F.obj P)) q)
        (by
          have hn := congrArg (fun k => homologyMap k q) (scalarModuleHom_precompose φ D i P)
          simp only [homologyMap_comp] at hn
          exact hn)
      retract := by
        apply Arrow.hom_ext
        · exact hs.trans hsId
        · exact ht'.trans htId }
  exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms (ModuleCat A')) a
    (by infer_instance)

lemma scalarModuleHom_quasiIso_of_homotopyCategoryRetract
    {M N : ModuleCategory A D}
    (a : Retract ((moduleToHomotopy A D).obj M) ((moduleToHomotopy A D).obj N))
    (P : ModuleCategory A D)
    (hN : QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) P))) :
    QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) P)) := by
  obtain ⟨i, hi⟩ := (moduleToHomotopy A D).map_surjective a.i
  obtain ⟨r, hr⟩ := (moduleToHomotopy A D).map_surjective a.r
  apply scalarModuleHom_quasiIso_of_homotopyRetract φ D i r _ P hN
  rw [Functor.map_comp, hi, hr, a.retract]
  exact ((moduleToHomotopy A D).map_id M).symm

/-- 任意の終域に対し全次数Hom係数変更比較が擬同型となる始域の性質。 -/
def scalarModuleHomComparisonLocus : ObjectProperty (ModuleHomotopyCategory A D) :=
  fun X => ∀ P : ModuleCategory A D,
    QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) X.as)
      (ForgetEnrichment.to (Complex A) P))

instance scalarModuleHomComparisonLocusStableUnderRetracts :
    (scalarModuleHomComparisonLocus φ D).IsStableUnderRetracts where
  of_retract a hN P := scalarModuleHom_quasiIso_of_homotopyCategoryRetract φ D a P (hN P)

lemma scalarModuleHomComparisonLocus_representable (z : D) :
    scalarModuleHomComparisonLocus φ D
      ((moduleToHomotopy A D).obj (ForgetEnrichment.of (Complex A) (representable A z))) := by
  intro P
  change QuasiIso (scalarModuleHom φ D (representable A z) (ForgetEnrichment.to (Complex A) P))
  have := scalarModuleHom_representable_isIso φ D z (ForgetEnrichment.to (Complex A) P)
  infer_instance

end SerrePositivity.DifferentialGraded
end

end ScalarHomHomotopyRetracts

/-! ## ScalarHomElementComponents（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarHomElementComponents.lean） -/

/-! # Hom要素の係数拡大と各評価cochainの一致 -/

@[expose] public section ScalarHomElementComponents

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

lemma scalarHomComparison_one_eq_map {K L : Complex A} {p : ℤ} (f : Cochain K L p) :
    let := φ.toAlgebra
    (ScalarExtension.homComparison φ K L).f p ((1 : A') ⊗ₜ[A] f) =
      f.map (ModuleCat.extendScalars φ) := by
  let := φ.toAlgebra
  apply Cochain.ext
  intro i j h
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((ScalarExtension.homComparison φ K L).f p ((1 : A') ⊗ₜ[A] f)).v i j h
      ((1 : A') ⊗ₜ[A] x) =
    (ModuleCat.extendScalars φ).map (f.v i j h) ((1 : A') ⊗ₜ[A] x)
  erw [ScalarExtension.homComparison_apply φ K L p i j h f x,
    ModuleCat.ExtendScalars.map_tmul φ]

variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleHomElement_π_map {M N : RightModule A D} {p : ℤ}
    (f : GradedHom A M N p) (x : D) :
    (moduleHomπ A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D M) (ScalarExtension.rightModule φ D N) x).f p
        (scalarModuleHomElement φ D f) =
      ((moduleHomπ A D M N x).f p f).map (ModuleCat.extendScalars φ) := by
  let := φ.toAlgebra
  have h := congrArg (fun k => k.f p ((1 : A') ⊗ₜ[A] f)) (scalarModuleHom_π φ D M N x)
  change _ = (ScalarExtension.homComparison φ (M.obj (Opposite.op x))
      (N.obj (Opposite.op x))).f p
    ((ModuleCat.extendScalars φ).map ((moduleHomπ A D M N x).f p) ((1 : A') ⊗ₜ[A] f)) at h
  erw [ModuleCat.ExtendScalars.map_tmul φ] at h
  exact h.trans (scalarHomComparison_one_eq_map φ ((moduleHomπ A D M N x).f p f))

end SerrePositivity.DifferentialGraded
end

end ScalarHomElementComponents
