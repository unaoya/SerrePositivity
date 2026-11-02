module

public import SerrePositivity.DifferentialGraded.Endomorphism.Scalar.HomComparison
public import SerrePositivity.DifferentialGraded.Morita.Kernel
public import SerrePositivity.DifferentialGraded.Morita.Perfect
public import SerrePositivity.DifferentialGraded.Bimodule.Value
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.BalancedTensor
public import SerrePositivity.DifferentialGraded.Bimodule.Right
public import SerrePositivity.DifferentialGraded.Derived.BimoduleBasic
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionHomotopy
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements
public import SerrePositivity.DifferentialGraded.Module.EvaluationReflects
public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtension
public import SerrePositivity.DifferentialGraded.Derived.BimoduleModuleEquivalence
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKernel
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionNaturality

/-!
# Morita.ScalarExtension.KernelComparison

## 概要
kernel の通常・局所化係数変更と導来作用・増大比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## ScalarExtensionKernel（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernel.lean） -/

/-! # 実際の通常kernelの係数変更と左右の評価

係数変更したambient加群圏へのdg関手と、実際の係数変更加群圏への比較を合成する。
これは通常kernelの構成であり、underived係数変更が任意の擬同型を保つとは主張しない。
-/

@[expose] public section ScalarExtensionKernel
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

def scalarKernel : Bimodule A' (DGBaseChange φ E) (DGBaseChange φ D) :=
  (dgFunctor φ P.toFunctor).comp (scalarModuleDGFunctor φ E)

lemma scalarKernel_rightAt (d : D) :
    (scalarKernel φ D E P).rightAt d = rightModule φ E (P.rightAt d) := rfl

lemma scalarKernel_value (e : E) (d : D) :
    (scalarKernel φ D E P).value e d = (extension φ).obj (P.value e d) := rfl

/-- 全Hom作用も含め、係数変更後の左評価は元の左加群の係数変更に一致する。 -/
lemma scalarKernel_leftAt (e : E) :
    (scalarKernel φ D E P).leftAt e = leftModule φ D (P.leftAt e) := by
  apply EnrichedFunctor.ext (Complex A')
    (F := (scalarKernel φ D E P).leftAt e) (G := leftModule φ D (P.leftAt e)) (fun _ => rfl)
  intro d d'
  simp only [eqToHom_refl, Category.comp_id]
  change (extension φ).map (P.toFunctor.map d d') ≫
      scalarModuleHom φ E (P.rightAt d) (P.rightAt d') ≫
        moduleHomπ A' (DGBaseChange φ E) (rightModule φ E (P.rightAt d))
          (rightModule φ E (P.rightAt d')) e =
    (extension φ).map (P.toFunctor.map d d' ≫
      moduleHomπ A E (P.rightAt d) (P.rightAt d') e) ≫
        homComparison φ ((P.rightAt d).obj (Opposite.op e)) ((P.rightAt d').obj (Opposite.op e))
  rw [scalarModuleHom_π, ← Category.assoc, ← CategoryTheory.Functor.map_comp]

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernel

/-! ## ScalarExtensionKernelTensor（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelTensor.lean） -/

/-! # 実際のkernel導来作用とU12f係数変更の評価正方形

各出力評価eで実際の作用をU12d tensorへ自然に比較し、U12fのhPN・hP'をそのまま用いる。
核変数の局所化・核合成の比較をこのファイルの結論へ混ぜない。
-/

@[expose] public section ScalarExtensionKernelTensor
universe u v w z z'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)
  [HasDerivedCategory.{z} (ModuleCat.{u} A)] [HasDerivedCategory.{z'} (ModuleCat.{u} A')]

/-- 全ての主導来入力射に自然な、係数変更後のkernel作用評価。 -/
def scalarKernelTensorEvaluationIso (e : E) :
    kernelDerivedTensorOnBimodule A D E P ⋙ moduleDerivedEvaluation A E e ⋙
        complexDerivedExtension φ ≅
      moduleDerivedTensorRight A D (P.leftAt e) ⋙ complexDerivedExtension φ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (perfectKernelDerivedTensorEvaluationIso A D E P e) _

lemma scalarKernelTensorEvaluationIso_app (e : E) (X : DerivedModuleCategory A D) :
    (scalarKernelTensorEvaluationIso φ D E P e).hom.app X =
      (complexDerivedExtension φ).map
        ((perfectKernelDerivedTensorEvaluationIso A D E P e).hom.app X) := by
  simp only [scalarKernelTensorEvaluationIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Category.id_comp]

def scalarKernelTensorBaseChange (e : E) {M : ModuleCategory A D}
    (R : ModuleProjectiveResolution A D M)
    (hPN : complexKFlat A (BalancedTensor.obj A D
      (ForgetEnrichment.to (Complex A) R.obj) (P.leftAt e)))
    (hP' : moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A) R.obj))) :
    (complexDerivedExtension φ).obj
        ((moduleDerivedEvaluation A E e).obj
          ((kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M))) ≅
      (moduleDerivedTensorRight A' (DGBaseChange φ D) (leftModule φ D (P.leftAt e))).obj
        ((derivedExtension φ D).obj ((moduleToDerived A D).obj M)) :=
  (complexDerivedExtension φ).mapIso
      ((perfectKernelDerivedTensorEvaluationIso A D E P e).app ((moduleToDerived A D).obj M)) ≪≫
    derivedTensorBaseChange φ D R (P.leftAt e) hPN hP'

variable (hP : ∀ x : D, modulePerfect A E ((moduleToDerived A E).obj
  (ForgetEnrichment.of (Complex A) (P.rightAt x))))

def scalarPerfectKernelTensorEvaluationIso (e : E) :
    (perfectKernelAction A D E P hP ⋙ perfectModuleInclusion A E Set.univ ⋙
        moduleDerivedEvaluation A E e) ⋙ complexDerivedExtension φ ≅
      perfectModuleInclusion A D Set.univ ⋙ moduleDerivedTensorRight A D (P.leftAt e) ⋙
        complexDerivedExtension φ :=
  Functor.isoWhiskerRight (perfectKernelActionEvaluationIso A D E P hP e) _ ≪≫
    Functor.associator _ _ _

def scalarPerfectKernelTensorBaseChange (e : E) {M : ModuleCategory A D}
    (hM : modulePerfect A D ((moduleToDerived A D).obj M))
    (R : ModuleProjectiveResolution A D M)
    (hPN : complexKFlat A (BalancedTensor.obj A D
      (ForgetEnrichment.to (Complex A) R.obj) (P.leftAt e)))
    (hP' : moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A) R.obj))) :
    (complexDerivedExtension φ).obj
        ((moduleDerivedEvaluation A E e).obj
          ((perfectModuleInclusion A E Set.univ).obj
            ((perfectKernelAction A D E P hP).obj ⟨_, hM⟩))) ≅
      (moduleDerivedTensorRight A' (DGBaseChange φ D) (leftModule φ D (P.leftAt e))).obj
        ((derivedExtension φ D).obj ((moduleToDerived A D).obj M)) :=
  scalarKernelTensorBaseChange φ D E P e R hPN hP'

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelTensor

/-! ## ScalarExtensionKernelAction（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelAction.lean） -/

/-! # 係数変更した実際のkernel作用へのU12f評価比較

U12fの終域tensorを係数変更したkernelの主導来作用の評価と同定する。
sourceは複体の導来係数変更であり、dg加群の導来係数変更と評価の交換を無条件には仮定しない。
-/

@[expose] public section ScalarExtensionKernelAction
universe u v w z z'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)
  [HasDerivedCategory.{z} (ModuleCat.{u} A)] [HasDerivedCategory.{z'} (ModuleCat.{u} A')]

def scalarKernelActionBaseChange (e : E) {M : ModuleCategory A D}
    (R : ModuleProjectiveResolution A D M)
    (hPN : complexKFlat A (BalancedTensor.obj A D
      (ForgetEnrichment.to (Complex A) R.obj) (P.leftAt e)))
    (hP' : moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A) R.obj))) :
    (complexDerivedExtension φ).obj
        ((moduleDerivedEvaluation A E e).obj
          ((kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M))) ≅
      (moduleDerivedEvaluation A' (DGBaseChange φ E) e).obj
        ((kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P)).obj ((derivedExtension φ D).obj ((moduleToDerived A D).obj M))) :=
  scalarKernelTensorBaseChange φ D E P e R hPN hP' ≪≫ (by
    rw [← scalarKernel_leftAt φ D E P e]
    exact ((perfectKernelDerivedTensorEvaluationIso A' (DGBaseChange φ D) (DGBaseChange φ E)
      (scalarKernel φ D E P) e).app
        ((derivedExtension φ D).obj ((moduleToDerived A D).obj M))).symm)

def scalarPerfectKernelActionBaseChange
    (hP : ∀ x : D, modulePerfect A E ((moduleToDerived A E).obj
      (ForgetEnrichment.of (Complex A) (P.rightAt x))))
    (e : E) {M : ModuleCategory A D}
    (hM : modulePerfect A D ((moduleToDerived A D).obj M))
    (R : ModuleProjectiveResolution A D M)
    (hPN : complexKFlat A (BalancedTensor.obj A D
      (ForgetEnrichment.to (Complex A) R.obj) (P.leftAt e)))
    (hP' : moduleRelativeKFlat A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A) R.obj))) :
    (complexDerivedExtension φ).obj
        ((moduleDerivedEvaluation A E e).obj
          ((perfectModuleInclusion A E Set.univ).obj
            ((perfectKernelAction A D E P hP).obj ⟨_, hM⟩))) ≅
      (moduleDerivedEvaluation A' (DGBaseChange φ E) e).obj
        ((kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P)).obj ((derivedExtension φ D).obj ((moduleToDerived A D).obj M))) :=
  scalarKernelActionBaseChange φ D E P e R hPN hP'

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelAction

/-! ## ScalarExtensionKernelFunctor（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelFunctor.lean） -/

/-! # 通常kernelの全Hom自然な閉零射の係数変更 -/

@[expose] public section ScalarExtensionKernelFunctor
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 係数変更した右加群射の族は左Dの全Hom作用と可換する。 -/
def scalarKernelMap {P Q : BimoduleCategory A E D} (f : P ⟶ Q) :
    BimoduleCategory.of A' (DGBaseChange φ E) (DGBaseChange φ D)
        (scalarKernel φ D E (BimoduleCategory.underlying A E D P)) ⟶
      BimoduleCategory.of A' (DGBaseChange φ E) (DGBaseChange φ D)
        (scalarKernel φ D E (BimoduleCategory.underlying A E D Q)) :=
  ⟨fun d => (moduleExtension φ E).map (f.val d), by
    intro d d'
    change D at d
    change D at d'
    change (extension φ).map ((BimoduleCategory.underlying A E D P).toFunctor.map d d') ≫
        scalarModuleHom φ E _ _ ≫ eHomWhiskerLeft (Complex A') _
          ((moduleExtension φ E).map (f.val d')) =
      (extension φ).map ((BimoduleCategory.underlying A E D Q).toFunctor.map d d') ≫
        scalarModuleHom φ E _ _ ≫ eHomWhiskerRight (Complex A')
          ((moduleExtension φ E).map (f.val d)) _
    erw [← scalarModuleHom_postcompose φ E
      (ForgetEnrichment.of (Complex A) ((BimoduleCategory.underlying A E D P).rightAt d))
      (f.val d')]
    rw [← CategoryTheory.Functor.map_comp_assoc]
    change (extension φ).map
        ((BimoduleCategory.underlying A E D P).toFunctor.map d d' ≫
          moduleHomPostcompose A E _ _ _ (f.val d')) ≫ _ = _
    rw [f.property, CategoryTheory.Functor.map_comp, Category.assoc]
    exact congrArg (fun k => (extension φ).map
      ((BimoduleCategory.underlying A E D Q).toFunctor.map d d') ≫ k)
        (scalarModuleHom_precompose φ E (f.val d) _)
  ⟩

def scalarKernelFunctor : BimoduleCategory A E D ⥤
    BimoduleCategory A' (DGBaseChange φ E) (DGBaseChange φ D) where
  obj P := BimoduleCategory.of A' (DGBaseChange φ E) (DGBaseChange φ D)
    (scalarKernel φ D E (BimoduleCategory.underlying A E D P))
  map f := scalarKernelMap φ D E f
  map_id P := by
    apply Subtype.ext
    funext d
    exact (moduleExtension φ E).map_id _
  map_comp f g := by
    apply Subtype.ext
    funext d
    exact (moduleExtension φ E).map_comp (f.val d) (g.val d)

lemma scalarKernelMap_value {P Q : BimoduleCategory A E D} (f : P ⟶ Q)
    (e : E) (d : D) :
    (BimoduleCategory.valueEvaluation A' (DGBaseChange φ E) (DGBaseChange φ D) e d).map
        (scalarKernelMap φ D E f) =
      (extension φ).map ((BimoduleCategory.valueEvaluation A E D e d).map f) :=
  moduleExtension_eval φ E (f.val d) e

variable [Small.{u} D]

/-- 左評価と通常kernelの係数変更は、kernel射にも自然に交換する。 -/
def scalarKernelLeftEvaluationIso (e : E) :
    scalarKernelFunctor φ D E ⋙
        BimoduleCategory.leftEvaluation A' (DGBaseChange φ E) (DGBaseChange φ D) e ≅
      BimoduleCategory.leftEvaluation A E D e ⋙ leftModuleExtension φ D :=
  NatIso.ofComponents
    (fun P => eqToIso (congrArg (ForgetEnrichment.of (Complex A'))
      (scalarKernel_leftAt φ D E (BimoduleCategory.underlying A E D P) e)))
    (by
      intro P Q f
      apply leftModuleMorphism_ext A' (DGBaseChange φ D)
      intro d
      simp only [CategoryTheory.Functor.map_comp, eqToIso.hom, eqToHom_map,
        eqToHom_refl]
      erw [Category.id_comp, Category.comp_id]
      change (leftModuleEvaluation A' (DGBaseChange φ D) d).map
          ((BimoduleCategory.leftEvaluation A' (DGBaseChange φ E)
            (DGBaseChange φ D) e).map (scalarKernelMap φ D E f)) =
        (leftModuleEvaluation A' (DGBaseChange φ D) d).map
          ((leftModuleExtension φ D).map ((BimoduleCategory.leftEvaluation A E D e).map f))
      rw [BimoduleCategory.leftEvaluation_map_eval, scalarKernelMap_value,
        leftModuleExtension_eval, BimoduleCategory.leftEvaluation_map_eval])

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelFunctor

/-! ## ScalarExtensionKernelProduct（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelProduct.lean） -/

/-! # 積dg圏のH⁰から主導来kernelへの非flatな係数変更

標準cylinderの射影だけを反転してH⁰へ降ろす。
通常の係数変更が任意のkernel擬同型を保存するとは仮定しない。
-/

@[expose] public section ScalarExtensionKernelProduct
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Opposite HomologicalComplex ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 積上の射の係数変更の擬同型性を、同じ値を持つ係数変更kernelへ運ぶ。 -/
lemma scalarKernelProduct_quasiIso
    {M N : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ} (f : M ⟶ N)
    (hf : moduleQuasiIso A' (DGBaseChange φ (DGTensorCategory A Eᵒᵖ D)ᵒᵖ)
      ((moduleExtension φ (DGTensorCategory A Eᵒᵖ D)ᵒᵖ).map f)) :
    BimoduleCategory.quasiIso A' (DGBaseChange φ E) (DGBaseChange φ D)
      ((scalarKernelFunctor φ D E).map ((rightModuleBimoduleEquivalence A E D).functor.map f)) := by
  intro e d
  erw [scalarKernelMap_value φ D E ((rightModuleBimoduleEquivalence A E D).functor.map f) e d]
  let α := rightModuleBimoduleEvaluationIso A E D e d
  have hq : QuasiIso ((extension φ).map
      ((moduleEvaluation A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ (op (op e, d))).map f)) := by
    simpa only [moduleExtension_eval] using hf (op (op e, d))
  have hn := congrArg (extension φ).map (α.hom.naturality f)
  simp only [Functor.comp_map, CategoryTheory.Functor.map_comp] at hn
  have ht : QuasiIso ((extension φ).map
      ((BimoduleCategory.valueEvaluation A E D e d).map
        ((rightModuleBimoduleEquivalence A E D).functor.map f)) ≫
      ((extension φ).mapIso (α.app N)).hom) := by
    erw [hn]
    infer_instance
  exact quasiIso_of_comp_right _ ((extension φ).mapIso (α.app N)).hom

lemma scalarKernelProduct_cylinder_quasiIso
    (M : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ) :
    BimoduleCategory.quasiIso A' (DGBaseChange φ E) (DGBaseChange φ D)
      ((scalarKernelFunctor φ D E).map
        ((rightModuleBimoduleEquivalence A E D).functor.map
          (modulePrecylinder A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M).π)) :=
  scalarKernelProduct_quasiIso φ D E _
    (moduleExtension_cylinder_quasiIso φ (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M)

/-- 積上の全dg自然な境界は、係数変更kernelの主局所化で等しくなる。 -/
lemma scalarKernelProduct_equalizes_boundary
    {M N : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ} (f g : M ⟶ N)
    (h : boundaryRelation A (RightModule A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ) f g) :
    (bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).map
        ((scalarKernelFunctor φ D E).map ((rightModuleBimoduleEquivalence A E D).functor.map f)) =
      (bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).map
        ((scalarKernelFunctor φ D E).map
          ((rightModuleBimoduleEquivalence A E D).functor.map g)) := by
  let F := (rightModuleBimoduleEquivalence A E D).functor ⋙ scalarKernelFunctor φ D E ⋙
    bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)
  let P := modulePrecylinder A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M
  let H := moduleCylinderLeftHomotopy A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ f g h
  have he : IsIso (F.map P.π) := bimoduleToDerived_inverts A'
    (DGBaseChange φ E) (DGBaseChange φ D) _ (scalarKernelProduct_cylinder_quasiIso φ D E M)
  let e := @asIso (DerivedBimoduleCategory A' (DGBaseChange φ E) (DGBaseChange φ D))
    _ _ _ (F.map P.π) he
  have hi : F.map P.i₀ = F.map P.i₁ := by
    have hs : F.map P.i₀ ≫ e.hom = F.map P.i₁ ≫ e.hom := by
      change F.map P.i₀ ≫ F.map P.π = F.map P.i₁ ≫ F.map P.π
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, P.i₀_π, P.i₁_π]
    have hc := congrArg (fun k => k ≫ e.inv) hs
    simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using hc
  change F.map f = F.map g
  calc
    F.map f = F.map (P.i₀ ≫ H.h) := congrArg F.map H.h₀.symm
    _ = F.map P.i₀ ≫ F.map H.h := F.map_comp _ _
    _ = F.map P.i₁ ≫ F.map H.h := congrArg (fun k => k ≫ F.map H.h) hi
    _ = F.map g := (F.map_comp _ _).symm.trans (congrArg F.map H.h₁)

/-- 積dg圏の主H⁰から係数変更後の主導来kernelへの実際の関手。 -/
def scalarKernelProductHomotopyToDerived :
    ModuleHomotopyCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ ⥤
      DerivedBimoduleCategory A' (DGBaseChange φ E) (DGBaseChange φ D) :=
  CategoryTheory.Quotient.lift _
    ((rightModuleBimoduleEquivalence A E D).functor ⋙ scalarKernelFunctor φ D E ⋙
      bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D))
    (fun _ _ f g h => scalarKernelProduct_equalizes_boundary φ D E f g h)

lemma scalarKernelProductHomotopyToDerived_fac :
    moduleToHomotopy A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ ⋙
        scalarKernelProductHomotopyToDerived φ D E =
      (rightModuleBimoduleEquivalence A E D).functor ⋙ scalarKernelFunctor φ D E ⋙
        bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D) :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- 積上のH⁰同型を、係数変更した実際のkernel対象間の同型として読む。 -/
def scalarKernelProductHomotopyMapIso
    {M N : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ}
    (e : (moduleToHomotopy A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ).obj M ≅
      (moduleToHomotopy A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ).obj N) :
    (bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).obj
        ((scalarKernelFunctor φ D E).obj ((rightModuleBimoduleEquivalence A E D).functor.obj M)) ≅
      (bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).obj
        ((scalarKernelFunctor φ D E).obj ((rightModuleBimoduleEquivalence A E D).functor.obj N)) :=
  (scalarKernelProductHomotopyToDerived φ D E).mapIso e

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelProduct

/-! ## ScalarExtensionKernelBalanced（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelBalanced.lean） -/

/-! # kernel作用のunderived係数変更を全Hom作用へ束ねる

複体の係数変更同型を左評価の比較と合成する。
全Hom自然性は係数変更・制限随伴を使い、元の係数環のcoend生成元上で検証する。
-/

@[expose] public section ScalarExtensionKernelBalanced
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
  ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarBalancedIso_element_one (M : RightModule A D) (N : LeftModule A D)
    (d : D) {r s n : ℤ} (m : (M.obj (op d)).X r) (v : (N.obj d).X s) (h : r + s = n) :
    let := φ.toAlgebra
    (balancedIso φ D M N).hom.f n ((1 : A') ⊗ₜ[A] BalancedTensor.element A D M N d m v h) =
      BalancedTensor.element A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) d
        ((1 : A') ⊗ₜ[A] m) ((1 : A') ⊗ₜ[A] v) h := by
  let := φ.toAlgebra
  have he := congrArg (fun k => k.f n
    ((1 : A') ⊗ₜ[A] ιTensorObj (M.obj (op d)) (N.obj d) r s n h (m ⊗ₜ[A] v)))
      (balancedIso_ι φ D M N d)
  change (balancedIso φ D M N).hom.f n
      (((extension φ).map (BalancedTensor.ι A D M N d)).f n
        ((1 : A') ⊗ₜ[A] ιTensorObj (M.obj (op d)) (N.obj d) r s n h (m ⊗ₜ[A] v))) =
    (BalancedTensor.ι A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) d).f n
      ((tensorIso φ (M.obj (op d)) (N.obj d)).hom.f n
        ((1 : A') ⊗ₜ[A] ιTensorObj (M.obj (op d)) (N.obj d) r s n h (m ⊗ₜ[A] v))) at he
  erw [ModuleCat.ExtendScalars.map_tmul φ,
    cochainTensorBaseChangeIso_apply_ι φ (M.obj (op d)) (N.obj d) r s n h] at he
  exact he

lemma scalarBalancedIso_map_element_one (M : RightModule A D) (N : LeftModule A D)
    (N' : LeftModuleCategory A' (DGBaseChange φ D))
    (g : ForgetEnrichment.of (Complex A') (leftModule φ D N) ⟶ N')
    (d : D) {r s n : ℤ} (m : (M.obj (op d)).X r) (v : (N.obj d).X s) (h : r + s = n) :
    let := φ.toAlgebra
    ((BalancedTensor.leftTensorFunctor A' (DGBaseChange φ D) (rightModule φ D M)).map g).f n
        ((balancedIso φ D M N).hom.f n
          ((1 : A') ⊗ₜ[A] BalancedTensor.element A D M N d m v h)) =
      BalancedTensor.element A' (DGBaseChange φ D) (rightModule φ D M)
        (ForgetEnrichment.to (Complex A') N') d ((1 : A') ⊗ₜ[A] m)
          (((leftModuleEvaluation A' (DGBaseChange φ D) d).map g).f s ((1 : A') ⊗ₜ[A] v)) h := by
  let := φ.toAlgebra
  rw [scalarBalancedIso_element_one φ D M N d m v h]
  dsimp only [BalancedTensor.leftTensorFunctor]
  erw [BalancedTensor.map_element]
  erw [CategoryTheory.Functor.map_id]
  rfl

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (P : Bimodule A E D) (M : RightModule A D)

/-- 全Hom付き左評価の同一視を、閉零左加群の同型として読む。 -/
def scalarKernelLeftValueIso (e : E) :
    ForgetEnrichment.of (Complex A') ((scalarKernel φ D E P).leftAt e) ≅
      ForgetEnrichment.of (Complex A') (leftModule φ D (P.leftAt e)) :=
  eqToIso (congrArg (ForgetEnrichment.of (Complex A')) (scalarKernel_leftAt φ D E P e))

def scalarKernelBalancedValueIso (e : E) :
    (extension φ).obj (BalancedTensor.obj A D M (P.leftAt e)) ≅
      BalancedTensor.obj A' (DGBaseChange φ D) (rightModule φ D M)
        ((scalarKernel φ D E P).leftAt e) :=
  balancedIso φ D M (P.leftAt e) ≪≫
    ((BalancedTensor.leftTensorFunctor A' (DGBaseChange φ D) (rightModule φ D M)).mapIso
      (scalarKernelLeftValueIso φ D E P e)).symm

lemma scalarKernelLeftValueIso_inv_eval (e : E) (d : D) :
    (leftModuleEvaluation A' (DGBaseChange φ D) d).map
        (scalarKernelLeftValueIso φ D E P e).inv = 𝟙 _ := by
  simp only [scalarKernelLeftValueIso, eqToIso.inv, eqToHom_map, eqToHom_refl]

lemma scalarKernelLeftValueIso_inv_eval_one (e : E) (d : D) (s : ℤ)
    (v : (P.value e d).X s) :
    let := φ.toAlgebra
    (((leftModuleEvaluation A' (DGBaseChange φ D) d).map
      (scalarKernelLeftValueIso φ D E P e).inv).f s)
        ((1 : A') ⊗ₜ[A] v) = (1 : A') ⊗ₜ[A] v := by
  let := φ.toAlgebra
  rw [scalarKernelLeftValueIso_inv_eval φ D E P e d]
  rfl

lemma scalarKernelBalancedValueIso_element_one (e : E) (d : D) {r s n : ℤ}
    (m : (M.obj (op d)).X r) (v : (P.value e d).X s) (h : r + s = n) :
    let := φ.toAlgebra
    (scalarKernelBalancedValueIso φ D E P M e).hom.f n
        ((1 : A') ⊗ₜ[A] BalancedTensor.element A D M (P.leftAt e) d m v h) =
      BalancedTensor.element A' (DGBaseChange φ D) (rightModule φ D M)
        ((scalarKernel φ D E P).leftAt e) d ((1 : A') ⊗ₜ[A] m) ((1 : A') ⊗ₜ[A] v) h := by
  let := φ.toAlgebra
  have he := scalarBalancedIso_map_element_one φ D M (P.leftAt e)
    (ForgetEnrichment.of (Complex A') ((scalarKernel φ D E P).leftAt e))
    (scalarKernelLeftValueIso φ D E P e).inv d m v h
  rw [scalarKernelLeftValueIso_inv_eval_one φ D E P e d s v] at he
  simp only [scalarKernelBalancedValueIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, HomologicalComplex.comp_f, ModuleCat.comp_apply]
  exact he

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelBalanced

/-! ## ScalarExtensionKernelBalancedModule（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelBalancedModule.lean） -/

/-! # 係数変更したkernel作用の全Hom自然な加群比較

比較を係数制限側で構成し、既存の加群係数変更随伴で戻す。
-/

@[expose] public section ScalarExtensionKernelBalancedModule
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
  ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (P : Bimodule A E D) (M : RightModule A D)

def scalarKernelBalancedUnitComponent (e : E) :
    BalancedTensor.obj A D M (P.leftAt e) ⟶
      (restriction φ).obj (BalancedTensor.obj A' (DGBaseChange φ D)
        (rightModule φ D M) ((scalarKernel φ D E P).leftAt e)) :=
  (adjunction φ).unit.app _ ≫ (restriction φ).map (scalarKernelBalancedValueIso φ D E P M e).hom

lemma scalarKernelBalancedUnitComponent_element (e : E) (d : D) {r s n : ℤ}
    (m : (M.obj (op d)).X r) (v : (P.value e d).X s) (h : r + s = n) :
    let := φ.toAlgebra
    (scalarKernelBalancedUnitComponent φ D E P M e).f n
        (BalancedTensor.element A D M (P.leftAt e) d m v h) =
      BalancedTensor.element A' (DGBaseChange φ D) (rightModule φ D M)
        ((scalarKernel φ D E P).leftAt e) d ((1 : A') ⊗ₜ[A] m) ((1 : A') ⊗ₜ[A] v) h := by
  let := φ.toAlgebra
  exact scalarKernelBalancedValueIso_element_one φ D E P M e d m v h

lemma scalarKernelBalancedUnit_naturality (x y : Eᵒᵖ) :
    ((kernelTensor A D E P).obj M).map x y ≫
        homPostcompose (((kernelTensor A D E P).obj M).obj x)
          (scalarKernelBalancedUnitComponent φ D E P M y.unop) =
      (rightRestriction φ E ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
        (scalarKernel φ D E P)).obj (rightModule φ D M))).map x y ≫
        homPrecompose (scalarKernelBalancedUnitComponent φ D E P M x.unop)
          ((rightRestriction φ E ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
            (scalarKernel φ D E P)).obj (rightModule φ D M))).obj y) := by
  let := φ.toAlgebra
  apply BalancedTensor.homMap_post_pre_eq A D M (P.leftAt x.unop)
  intro p f d r s i n hi hn m v
  change (scalarKernelBalancedUnitComponent φ D E P M y.unop).f n
      (moduleAction A ((kernelTensor A D E P).obj M) (x := x) (y := y) f
        (BalancedTensor.element A D M (P.leftAt x.unop) d m v hi) hn) =
    moduleAction A (rightRestriction φ E
      ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)).obj
        (rightModule φ D M))) (x := x) (y := y) f
      ((scalarKernelBalancedUnitComponent φ D E P M x.unop).f i
        (BalancedTensor.element A D M (P.leftAt x.unop) d m v hi)) hn
  erw [BimoduleTensor.compose_rightAction_element A E D (RightModule A D) P
    (DGFunctor.id (RightModule A D)) x y d M hi rfl hn f m v]
  dsimp only [Bimodule.rightAt, DGFunctor.id]
  simp only [Units.smul_def, map_zsmul]
  have hy := scalarKernelBalancedUnitComponent_element φ D E P M y.unop d
    (r := r) (s := s + p) (n := n) m
    (moduleAction A (P.rightAt d) (x := x) (y := y) f v (rfl : s + p = s + p))
    (by omega : r + (s + p) = n)
  have hx := scalarKernelBalancedUnitComponent_element φ D E P M x.unop d
    (r := r) (s := s) (n := i) m v hi
  have hl := congrArg (fun z => (p * r).negOnePow.val • z) hy
  have hr := congrArg (fun z => moduleAction A
    (rightRestriction φ E
      ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)).obj
        (rightModule φ D M))) (x := x) (y := y) f z hn) hx
  refine hl.trans (Eq.trans ?_ hr.symm)
  have hrest := rightRestriction_action φ E
    ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)).obj
      (rightModule φ D M)) x y p i n hn f
    (BalancedTensor.element A' (DGBaseChange φ D) (rightModule φ D M)
      ((scalarKernel φ D E P).leftAt x.unop) d ((1 : A') ⊗ₜ[A] m) ((1 : A') ⊗ₜ[A] v) hi)
  erw [hrest]
  erw [BimoduleTensor.compose_rightAction_element A' (DGBaseChange φ E) (DGBaseChange φ D)
    (RightModule A' (DGBaseChange φ D)) (scalarKernel φ D E P)
    (DGFunctor.id (RightModule A' (DGBaseChange φ D))) x y d (rightModule φ D M)
    hi rfl hn ((1 : A') ⊗ₜ[A] f) ((1 : A') ⊗ₜ[A] m) ((1 : A') ⊗ₜ[A] v)]
  erw [rightModule_action φ E (P.rightAt d) x y p s (s + p) rfl f v]
  rfl

def scalarKernelBalancedUnit :
    ForgetEnrichment.of (Complex A) ((kernelTensor A D E P).obj M) ⟶
      (ScalarExtension.moduleRestriction φ E).obj
        (ForgetEnrichment.of (Complex A')
          ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
            (scalarKernel φ D E P)).obj (rightModule φ D M))) :=
  moduleMorphismMk A E
    (M := (kernelTensor A D E P).obj M)
    (N := rightRestriction φ E
      ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)).obj
        (rightModule φ D M)))
    (fun x => scalarKernelBalancedUnitComponent φ D E P M x.unop)
    (scalarKernelBalancedUnit_naturality φ D E P M)

lemma scalarKernelBalancedUnit_eval (e : E) :
    (moduleEvaluation A E e).map (scalarKernelBalancedUnit φ D E P M) =
      scalarKernelBalancedUnitComponent φ D E P M e :=
  moduleMorphismMk_eval A E _ _ e

/-- 随伴により戻した、実際の係数変更加群圏の比較射。 -/
def scalarKernelBalancedMap :
    (moduleExtension φ E).obj (ForgetEnrichment.of (Complex A) ((kernelTensor A D E P).obj M)) ⟶
      ForgetEnrichment.of (Complex A')
        ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P)).obj (rightModule φ D M)) :=
  ((moduleAdjunction φ E).homEquiv _ _).symm (scalarKernelBalancedUnit φ D E P M)

lemma scalarKernelBalancedMap_eval (e : E) :
    (moduleEvaluation A' (DGBaseChange φ E) e).map (scalarKernelBalancedMap φ D E P M) =
      (scalarKernelBalancedValueIso φ D E P M e).hom := by
  rw [scalarKernelBalancedMap, Adjunction.homEquiv_counit, CategoryTheory.Functor.map_comp]
  change (moduleEvaluation A' (DGBaseChange φ E) e).map
      ((moduleExtension φ E).map (scalarKernelBalancedUnit φ D E P M)) ≫
      (moduleEvaluation A' (DGBaseChange φ E) e).map (moduleCounitApp φ E _) = _
  rw [moduleExtension_eval, scalarKernelBalancedUnit_eval, moduleCounitApp_eval]
  change (extension φ).map
      ((adjunction φ).unit.app (BalancedTensor.obj A D M (P.leftAt e)) ≫
        (restriction φ).map (scalarKernelBalancedValueIso φ D E P M e).hom) ≫
      (adjunction φ).counit.app _ = _
  rw [CategoryTheory.Functor.map_comp, Category.assoc]
  have h := (adjunction φ).counit.naturality (scalarKernelBalancedValueIso φ D E P M e).hom
  simp only [Functor.comp_map, Functor.id_map] at h
  erw [h]
  rw [← Category.assoc]
  erw [(adjunction φ).left_triangle_components (BalancedTensor.obj A D M (P.leftAt e))]
  exact Category.id_comp _

/-- 任意の環準同型に対する、kernel作用のunderived係数変更の実際の加群同型。 -/
def scalarKernelBalancedIso :
    (moduleExtension φ E).obj (ForgetEnrichment.of (Complex A) ((kernelTensor A D E P).obj M)) ≅
      ForgetEnrichment.of (Complex A')
        ((kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P)).obj (rightModule φ D M)) := by
  have : IsIso (scalarKernelBalancedMap φ D E P M) :=
    moduleIsIso_of_evaluations A' (DGBaseChange φ E) _ (fun e => by
      rw [scalarKernelBalancedMap_eval]
      infer_instance)
  exact asIso (scalarKernelBalancedMap φ D E P M)

lemma scalarKernelBalancedIso_hom_eval (e : E) :
    (moduleEvaluation A' (DGBaseChange φ E) e).map (scalarKernelBalancedIso φ D E P M).hom =
      (scalarKernelBalancedValueIso φ D E P M e).hom :=
  scalarKernelBalancedMap_eval φ D E P M e

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelBalancedModule

/-! ## ScalarExtensionKernelBalancedNaturality（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelBalancedNaturality.lean） -/

/-! # kernel作用のunderived係数変更の入力自然性 -/

@[expose] public section ScalarExtensionKernelBalancedNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

lemma scalarKernelBalancedValueIso_right_naturality
    {M N : ModuleCategory A D} (f : M ⟶ N) (e : E) :
    (extension φ).map ((BalancedTensor.rightTensorFunctor A D (P.leftAt e)).map f) ≫
        (scalarKernelBalancedValueIso φ D E P (ForgetEnrichment.to (Complex A) N) e).hom =
      (scalarKernelBalancedValueIso φ D E P (ForgetEnrichment.to (Complex A) M) e).hom ≫
        (BalancedTensor.rightTensorFunctor A' (DGBaseChange φ D)
          ((scalarKernel φ D E P).leftAt e)).map ((moduleExtension φ D).map f) := by
  have hb := balancedIso_module_naturality φ D f
    (𝟙 (ForgetEnrichment.of (Complex A) (P.leftAt e)))
  simp only [CategoryTheory.Functor.map_id] at hb
  have hn := (BalancedTensor.rightTensorLeftMap A' (DGBaseChange φ D)
    (scalarKernelLeftValueIso φ D E P e).inv).naturality ((moduleExtension φ D).map f)
  simp only [scalarKernelBalancedValueIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
  rw [← Category.assoc]
  erw [hb]
  rw [Category.assoc, Category.assoc]
  congr 1

lemma scalarKernelBalancedIso_right_naturality
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleExtension φ E).map ((kernelTensor A D E P).onClosed.map f) ≫
        (scalarKernelBalancedIso φ D E P (ForgetEnrichment.to (Complex A) N)).hom =
      (scalarKernelBalancedIso φ D E P (ForgetEnrichment.to (Complex A) M)).hom ≫
        (kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P)).onClosed.map ((moduleExtension φ D).map f) := by
  apply moduleMorphism_ext
  intro e
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    moduleExtension_eval, scalarKernelBalancedIso_hom_eval, scalarKernelBalancedIso_hom_eval,
    perfectKernelTensor_map_eval, perfectKernelTensor_map_eval]
  exact scalarKernelBalancedValueIso_right_naturality φ D E P f e

/-- 全閉零入力射に自然な、実際のdg加群値の係数変更比較。 -/
def scalarKernelBalancedNatIso :
    (kernelTensor A D E P).onClosed ⋙ moduleExtension φ E ≅
      moduleExtension φ D ⋙
        (kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)).onClosed :=
  NatIso.ofComponents
    (fun M => scalarKernelBalancedIso φ D E P (ForgetEnrichment.to (Complex A) M))
    (by intro M N f; exact scalarKernelBalancedIso_right_naturality φ D E P f)

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelBalancedNaturality

/-! ## ScalarExtensionKernelHomotopy（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelHomotopy.lean） -/

/-! # kernel係数変更比較のH⁰降下と主導来値への接続 -/

@[expose] public section ScalarExtensionKernelHomotopy
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- 通常入力上で、二つのH⁰関手の前合成を実際の加群比較で同定する。 -/
def scalarKernelBalancedHomotopyFacIso :
    moduleToHomotopy A D ⋙ (kernelTensor A D E P).onHomotopy ⋙
        scalarModuleExtensionHomotopy φ E ≅
      moduleToHomotopy A D ⋙ scalarModuleExtensionHomotopy φ D ⋙
        (kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)).onHomotopy :=
  Functor.isoWhiskerRight (eqToIso (kernelTensor A D E P).onHomotopy_fac)
      (scalarModuleExtensionHomotopy φ E) ≪≫
    Functor.isoWhiskerLeft (kernelTensor A D E P).onClosed
      (eqToIso (scalarModuleExtensionHomotopy_fac φ E)) ≪≫
    Functor.isoWhiskerRight (scalarKernelBalancedNatIso φ D E P)
      (moduleToHomotopy A' (DGBaseChange φ E)) ≪≫
    Functor.isoWhiskerLeft (moduleExtension φ D)
      (eqToIso (kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E)
        (scalarKernel φ D E P)).onHomotopy_fac).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (scalarModuleExtensionHomotopy_fac φ D)).symm
      (kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)).onHomotopy

/-- 全てのH⁰入力射に自然な、係数変更とkernel作用の比較。 -/
def scalarKernelBalancedHomotopyIso :
    (kernelTensor A D E P).onHomotopy ⋙ scalarModuleExtensionHomotopy φ E ≅
      scalarModuleExtensionHomotopy φ D ⋙
        (kernelTensor A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)).onHomotopy :=
  Quotient.natIsoLift (boundaryRelation A (RightModule A D))
    (scalarKernelBalancedHomotopyFacIso φ D E P)

/-- 既存の二つの係数変更ホモトピー関手は、主導来値へ送ると自然に一致する。 -/
def scalarExtensionHomotopyDerivedIso :
    scalarModuleExtensionHomotopy φ D ⋙ moduleHomotopyToDerivedClosed A' (DGBaseChange φ D) ≅
      moduleExtensionHomotopyToDerived φ D :=
  Quotient.natIsoLift (boundaryRelation A (RightModule A D))
    (Functor.isoWhiskerRight (eqToIso (scalarModuleExtensionHomotopy_fac φ D))
        (moduleHomotopyToDerivedClosed A' (DGBaseChange φ D)) ≪≫
      Functor.isoWhiskerLeft (moduleExtension φ D)
        (moduleToHomotopyDerivedIso A' (DGBaseChange φ D)) ≪≫
      (eqToIso (moduleExtensionHomotopyToDerived_fac φ D)).symm)

/-- H⁰のkernel係数変更比較を、実際の主導来値の関手へ送る。 -/
def scalarKernelBalancedHomotopyDerivedIso :
    (kernelTensor A D E P).onHomotopy ⋙ moduleExtensionHomotopyToDerived φ E ≅
      scalarModuleExtensionHomotopy φ D ⋙
        kernelHomotopyToDerived A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P) :=
  Functor.isoWhiskerLeft (kernelTensor A D E P).onHomotopy
      (scalarExtensionHomotopyDerivedIso φ E).symm ≪≫
    Functor.isoWhiskerRight (scalarKernelBalancedHomotopyIso φ D E P)
      (moduleHomotopyToDerivedClosed A' (DGBaseChange φ E))

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelHomotopy

/-! ## ScalarExtensionKernelLocalization（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelLocalization.lean） -/

/-! # 任意可換環上の主導来kernelの係数変更

既存の積上の右加群との主導来同値と射影解像度関手を使う。
通常kernelの係数変更を任意の擬同型へ直接適用することはしない。
-/

@[expose] public section ScalarExtensionKernelLocalization
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Opposite ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 積上の指定射影解像度族で計算する、全主導来kernel射上の係数変更関手。 -/
def scalarKernelResolutionExtension
    (R : ∀ M : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ,
      ModuleProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M) :
    DerivedBimoduleCategory A E D ⥤
      DerivedBimoduleCategory A' (DGBaseChange φ E) (DGBaseChange φ D) :=
  (rightModuleBimoduleDerivedEquivalence A E D).inverse ⋙
    moduleDerivedResolutionFunctor A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ R ⋙
      scalarKernelProductHomotopyToDerived φ D E

/-- 標準semifree解像度による主導来kernelの非flatな係数変更。 -/
def scalarKernelDerivedExtension : DerivedBimoduleCategory A E D ⥤
    DerivedBimoduleCategory A' (DGBaseChange φ E) (DGBaseChange φ D) :=
  scalarKernelResolutionExtension φ D E
    (moduleCanonicalProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ)

/-- 通常kernelでの計算を、全閉零kernel射に自然な同型として与える。 -/
def scalarKernelResolutionExtensionFacIso
    (R : ∀ M : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ,
      ModuleProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M) :
    bimoduleToDerived A E D ⋙ scalarKernelResolutionExtension φ D E R ≅
      (rightModuleBimoduleEquivalence A E D).inverse ⋙
        moduleResolutionHomotopyFunctor A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ R ⋙
          scalarKernelProductHomotopyToDerived φ D E :=
  Functor.isoWhiskerRight (rightModuleBimoduleDerived_inverse_fac A E D)
      (moduleDerivedResolutionFunctor A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ R ⋙
        scalarKernelProductHomotopyToDerived φ D E) ≪≫
    Functor.isoWhiskerLeft (rightModuleBimoduleEquivalence A E D).inverse
      (Functor.isoWhiskerRight (moduleDerivedResolutionFunctor_fac A
        (DGTensorCategory A Eᵒᵖ D)ᵒᵖ R) (scalarKernelProductHomotopyToDerived φ D E))

/-- 元のkernelの積上の解像度を係数変更した、実際の主局所化の対象で計算する。 -/
def scalarKernelResolutionExtensionComputation
    (R : ∀ M : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ,
      ModuleProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M)
    (P : BimoduleCategory A E D) :
    (scalarKernelResolutionExtension φ D E R).obj ((bimoduleToDerived A E D).obj P) ≅
      (bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).obj
        ((scalarKernelFunctor φ D E).obj ((rightModuleBimoduleEquivalence A E D).functor.obj
          (R ((rightModuleBimoduleEquivalence A E D).inverse.obj P)).obj)) :=
  (scalarKernelResolutionExtensionFacIso φ D E R).app P

/-- 解像度族の変更を全主導来kernel射に自然な同型で比較する。 -/
def scalarKernelResolutionExtensionIso
    (R S : ∀ M : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ,
      ModuleProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M) :
    scalarKernelResolutionExtension φ D E R ≅ scalarKernelResolutionExtension φ D E S :=
  Functor.isoWhiskerLeft (rightModuleBimoduleDerivedEquivalence A E D).inverse
    (Functor.isoWhiskerRight (moduleDerivedResolutionIso A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ R S)
      (scalarKernelProductHomotopyToDerived φ D E))

lemma scalarKernelResolutionExtensionIso_self
    (R : ∀ M : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ,
      ModuleProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M) :
    scalarKernelResolutionExtensionIso φ D E R R = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (scalarKernelProductHomotopyToDerived φ D E).map
    ((moduleDerivedResolutionIso A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ R R).hom.app _) = 𝟙 _
  rw [moduleDerivedResolutionIso_self]
  exact (scalarKernelProductHomotopyToDerived φ D E).map_id _

lemma scalarKernelResolutionExtensionIso_trans
    (R S T : ∀ M : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ,
      ModuleProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M) :
    scalarKernelResolutionExtensionIso φ D E R S ≪≫ scalarKernelResolutionExtensionIso φ D E S T =
      scalarKernelResolutionExtensionIso φ D E R T := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  change (scalarKernelProductHomotopyToDerived φ D E).map
      ((moduleDerivedResolutionIso A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ R S).hom.app _) ≫
      (scalarKernelProductHomotopyToDerived φ D E).map
        ((moduleDerivedResolutionIso A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ S T).hom.app _) = _
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg (scalarKernelProductHomotopyToDerived φ D E).map
    (NatTrans.congr_app (congrArg Iso.hom
      (moduleDerivedResolutionIso_trans A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ R S T)) _)

/-- 任意の証明付き積上射影解像度で、標準導来kernel係数変更を計算する。 -/
def scalarKernelDerivedExtensionResolutionComputation {P : BimoduleCategory A E D}
    (R : ModuleProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ
      ((rightModuleBimoduleEquivalence A E D).inverse.obj P)) :
    (scalarKernelDerivedExtension φ D E).obj ((bimoduleToDerived A E D).obj P) ≅
      (bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).obj
        ((scalarKernelFunctor φ D E).obj
          ((rightModuleBimoduleEquivalence A E D).functor.obj R.obj)) := by
  let R₀ := moduleCanonicalProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ
  exact scalarKernelResolutionExtensionComputation φ D E R₀ P ≪≫
    scalarKernelProductHomotopyMapIso φ D E
      (@asIso _ _ _ _ ((moduleToHomotopy A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ).map
        ((R₀ ((rightModuleBimoduleEquivalence A E D).inverse.obj P)).comparison R))
        ((R₀ ((rightModuleBimoduleEquivalence A E D).inverse.obj P)).comparison_isIso_homotopy R))

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelLocalization

/-! ## ScalarExtensionKernelLocalizationAugmentation（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelLocalizationAugmentation.lean） -/

/-! # 主導来kernel係数変更から通常モデルへの自然な増大比較

比較射の構成と可逆性のモデル条件を分ける。
-/

@[expose] public section ScalarExtensionKernelLocalizationAugmentation
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Opposite ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

lemma scalarKernelProductHomotopyToDerived_map_closed
    {M N : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ} (f : M ⟶ N) :
    (scalarKernelProductHomotopyToDerived φ D E).map
        ((moduleToHomotopy A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ).map f) =
      (bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).map
        ((scalarKernelFunctor φ D E).map ((rightModuleBimoduleEquivalence A E D).functor.map f)) :=
  rfl

/-- 任意の積上解像度族の増大を、通常kernelの全閉零射に自然に送る。 -/
def scalarKernelResolutionAugmentation
    (R : ∀ M : ModuleCategory A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ,
      ModuleProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ M) :
    (rightModuleBimoduleEquivalence A E D).inverse ⋙
        moduleResolutionHomotopyFunctor A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ R ⋙
          scalarKernelProductHomotopyToDerived φ D E ⟶
      scalarKernelFunctor φ D E ⋙ bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D) where
  app P := (scalarKernelFunctor φ D E ⋙
    bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).map
      ((rightModuleBimoduleEquivalence A E D).functor.map
          (R ((rightModuleBimoduleEquivalence A E D).inverse.obj P)).π ≫
        ((rightModuleBimoduleEquivalence A E D).counitIso.app P).hom)
  naturality {P Q} f := by
    let H := rightModuleBimoduleEquivalence A E D
    let G := scalarKernelFunctor φ D E ⋙
      bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)
    let F := H.functor ⋙ G
    have h := congrArg (scalarKernelProductHomotopyToDerived φ D E).map
      ((R (H.inverse.obj P)).lift_fac (R (H.inverse.obj Q)) (H.inverse.map f))
    simp only [CategoryTheory.Functor.map_comp,
      scalarKernelProductHomotopyToDerived_map_closed] at h
    have hn := congrArg G.map (H.counitIso.hom.naturality f)
    simp only [Functor.comp_map, CategoryTheory.Functor.map_comp] at hn
    change F.map ((R (H.inverse.obj P)).lift (R (H.inverse.obj Q)) (H.inverse.map f)) ≫
        G.map (H.functor.map (R (H.inverse.obj Q)).π ≫ (H.counitIso.app Q).hom) =
      G.map (H.functor.map (R (H.inverse.obj P)).π ≫ (H.counitIso.app P).hom) ≫ G.map f
    simp only [CategoryTheory.Functor.map_comp]
    rw [← Category.assoc]
    erw [h]
    rw [Category.assoc]
    erw [hn]
    exact (Category.assoc _ _ _).symm

/-- 主導来kernel係数変更を通常kernelの係数変更へ比較する自然変換。 -/
def scalarKernelDerivedExtensionAugmentation :
    bimoduleToDerived A E D ⋙ scalarKernelDerivedExtension φ D E ⟶
      scalarKernelFunctor φ D E ⋙ bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D) :=
  (scalarKernelResolutionExtensionFacIso φ D E
      (moduleCanonicalProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ)).hom ≫
    scalarKernelResolutionAugmentation φ D E
      (moduleCanonicalProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ)

lemma scalarKernelDerivedExtensionAugmentation_app (P : BimoduleCategory A E D) :
    (scalarKernelDerivedExtensionAugmentation φ D E).app P =
      (scalarKernelResolutionExtensionComputation φ D E
        (moduleCanonicalProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ) P).hom ≫
        (scalarKernelFunctor φ D E ⋙
          bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).map
          ((rightModuleBimoduleEquivalence A E D).functor.map
              (moduleCanonicalProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ
                ((rightModuleBimoduleEquivalence A E D).inverse.obj P)).π ≫
            ((rightModuleBimoduleEquivalence A E D).counitIso.app P).hom) := rfl

/-- 比較の可逆性には、選んだ積上モデルの増大が係数変更後も擬同型となる条件を保持する。 -/
lemma scalarKernelDerivedExtensionAugmentation_isIso (P : BimoduleCategory A E D)
    (hπ : BimoduleCategory.quasiIso A' (DGBaseChange φ E) (DGBaseChange φ D)
      ((scalarKernelFunctor φ D E).map
        ((rightModuleBimoduleEquivalence A E D).functor.map
            (moduleCanonicalProjectiveResolution A (DGTensorCategory A Eᵒᵖ D)ᵒᵖ
              ((rightModuleBimoduleEquivalence A E D).inverse.obj P)).π ≫
          ((rightModuleBimoduleEquivalence A E D).counitIso.app P).hom))) :
    IsIso ((scalarKernelDerivedExtensionAugmentation φ D E).app P) := by
  have := bimoduleToDerived_inverts A' (DGBaseChange φ E) (DGBaseChange φ D) _ hπ
  rw [scalarKernelDerivedExtensionAugmentation_app]
  change IsIso (_ ≫ (bimoduleToDerived A' (DGBaseChange φ E) (DGBaseChange φ D)).map _)
  infer_instance

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelLocalizationAugmentation

/-! ## ScalarExtensionKernelMapNaturality（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelMapNaturality.lean） -/

/-! # kernel射に関する実際のunderived係数変更比較の自然性 -/

@[expose] public section ScalarExtensionKernelMapNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  {P Q : BimoduleCategory A E D} (f : P ⟶ Q)

lemma scalarKernelLeftValueIso_kernel_naturality (e : E) :
    (leftModuleExtension φ D).map ((BimoduleCategory.leftEvaluation A E D e).map f) ≫
        (scalarKernelLeftValueIso φ D E (BimoduleCategory.underlying A E D Q) e).inv =
      (scalarKernelLeftValueIso φ D E (BimoduleCategory.underlying A E D P) e).inv ≫
        (BimoduleCategory.leftEvaluation A' (DGBaseChange φ E) (DGBaseChange φ D) e).map
          ((scalarKernelFunctor φ D E).map f) :=
by
  apply leftModuleMorphism_ext A' (DGBaseChange φ D)
  intro d
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  rw [leftModuleExtension_eval, BimoduleCategory.leftEvaluation_map_eval,
    BimoduleCategory.leftEvaluation_map_eval]
  erw [scalarKernelLeftValueIso_inv_eval φ D E (BimoduleCategory.underlying A E D Q) e d,
    scalarKernelLeftValueIso_inv_eval φ D E (BimoduleCategory.underlying A E D P) e d]
  erw [Category.comp_id, Category.id_comp]
  exact (scalarKernelMap_value φ D E f e d).symm

lemma scalarKernelBalancedValueIso_kernel_naturality (M : ModuleCategory A D) (e : E) :
    (extension φ).map (BalancedTensor.map A D (𝟙 M)
        ((BimoduleCategory.leftEvaluation A E D e).map f)) ≫
        (scalarKernelBalancedValueIso φ D E (BimoduleCategory.underlying A E D Q)
          (ForgetEnrichment.to (Complex A) M) e).hom =
      (scalarKernelBalancedValueIso φ D E (BimoduleCategory.underlying A E D P)
        (ForgetEnrichment.to (Complex A) M) e).hom ≫
        BalancedTensor.map A' (DGBaseChange φ D) (𝟙 ((moduleExtension φ D).obj M))
          ((BimoduleCategory.leftEvaluation A' (DGBaseChange φ E) (DGBaseChange φ D) e).map
            ((scalarKernelFunctor φ D E).map f)) := by
  have hb := balancedIso_module_naturality φ D (𝟙 M)
    ((BimoduleCategory.leftEvaluation A E D e).map f)
  simp only [CategoryTheory.Functor.map_id] at hb
  have he := congrArg
    (BalancedTensor.leftTensorFunctor A' (DGBaseChange φ D)
      (rightModule φ D (ForgetEnrichment.to (Complex A) M))).map
    (scalarKernelLeftValueIso_kernel_naturality φ D E f e)
  simp only [CategoryTheory.Functor.map_comp] at he
  simp only [scalarKernelBalancedValueIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
  rw [← Category.assoc]
  erw [hb]
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun k => (balancedIso φ D (ForgetEnrichment.to (Complex A) M)
    ((BimoduleCategory.underlying A E D P).leftAt e)).hom ≫ k) he

lemma scalarKernelBalancedIso_kernel_naturality (M : ModuleCategory A D) :
    (moduleExtension φ E).map ((kernelTensorMap A D E f).app M) ≫
        (scalarKernelBalancedIso φ D E (BimoduleCategory.underlying A E D Q)
          (ForgetEnrichment.to (Complex A) M)).hom =
      (scalarKernelBalancedIso φ D E (BimoduleCategory.underlying A E D P)
        (ForgetEnrichment.to (Complex A) M)).hom ≫
        (kernelTensorMap A' (DGBaseChange φ D) (DGBaseChange φ E)
          ((scalarKernelFunctor φ D E).map f)).app ((moduleExtension φ D).obj M) := by
  apply moduleMorphism_ext
  intro e
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    moduleExtension_eval, scalarKernelBalancedIso_hom_eval, scalarKernelBalancedIso_hom_eval,
    kernelTensorMap_value, kernelTensorMap_value]
  exact scalarKernelBalancedValueIso_kernel_naturality φ D E f M e

/-- 入力射への自然同型は、kernelの全閉零射にも自然。 -/
lemma scalarKernelBalancedNatIso_kernel_naturality :
    Functor.whiskerRight (kernelTensorMap A D E f) (moduleExtension φ E) ≫
        (scalarKernelBalancedNatIso φ D E (BimoduleCategory.underlying A E D Q)).hom =
      (scalarKernelBalancedNatIso φ D E (BimoduleCategory.underlying A E D P)).hom ≫
        Functor.whiskerLeft (moduleExtension φ D)
          (kernelTensorMap A' (DGBaseChange φ D) (DGBaseChange φ E)
            ((scalarKernelFunctor φ D E).map f)) := by
  apply NatTrans.ext
  funext M
  exact scalarKernelBalancedIso_kernel_naturality φ D E f M

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelMapNaturality

/-! ## ScalarExtensionKernelDerivedComparison（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelDerivedComparison.lean） -/

/-! # kernel係数変更を導来作用へ接続するH⁰増大比較

比較射の存在と可逆性を分ける。可逆性のモデル条件は明示して受け取る。
-/

@[expose] public section ScalarExtensionKernelDerivedComparison
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 導来係数変更から通常係数変更への比較を、全H⁰入力射へ降ろす。 -/
def scalarExtensionHomotopyAugmentation :
    moduleHomotopyToDerivedClosed A D ⋙ derivedExtension φ D ⟶
      moduleExtensionHomotopyToDerived φ D :=
  Quotient.natTransLift (boundaryRelation A (RightModule A D))
    (Functor.whiskerRight (moduleToHomotopyDerivedIso A D).hom (derivedExtension φ D) ≫
      derivedExtensionAugmentation φ D ≫
        eqToHom (moduleExtensionHomotopyToDerived_fac φ D).symm)

lemma scalarExtensionHomotopyAugmentation_app (M : ModuleCategory A D) :
    (scalarExtensionHomotopyAugmentation φ D).app ((moduleToHomotopy A D).obj M) =
      (derivedExtension φ D).map ((moduleToHomotopyDerivedIso A D).hom.app M) ≫
        (derivedExtensionAugmentation φ D).app M := by
  simp only [scalarExtensionHomotopyAugmentation, Quotient.natTransLift_app,
    NatTrans.comp_app, Functor.whiskerRight_app, eqToHom_refl, Category.comp_id]

lemma scalarExtensionHomotopyAugmentation_isIso (M : ModuleCategory A D)
    (hM : IsIso ((derivedExtensionAugmentation φ D).app M)) :
    IsIso ((scalarExtensionHomotopyAugmentation φ D).app ((moduleToHomotopy A D).obj M)) := by
  let := hM
  rw [scalarExtensionHomotopyAugmentation_app]
  infer_instance

variable (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- 主導来kernel作用から通常作用への増大を全H⁰入力射へ降ろす。 -/
def scalarKernelHomotopyAugmentation :
    moduleHomotopyToDerivedClosed A D ⋙ kernelDerivedTensorOnBimodule A D E P ⟶
      kernelHomotopyToDerived A D E P :=
  Quotient.natTransLift (boundaryRelation A (RightModule A D))
    (Functor.whiskerRight (moduleToHomotopyDerivedIso A D).hom
        (kernelDerivedTensorOnBimodule A D E P) ≫
      kernelDerivedTensorAugmentation A D E P ≫
        (kernelTensorHomotopyComputationIso A D E P).inv)

lemma scalarKernelHomotopyAugmentation_app (M : ModuleCategory A D) :
    (scalarKernelHomotopyAugmentation D E P).app ((moduleToHomotopy A D).obj M) =
      (kernelDerivedTensorOnBimodule A D E P).map ((moduleToHomotopyDerivedIso A D).hom.app M) ≫
        (kernelDerivedTensorAugmentation A D E P).app M ≫
          (kernelTensorHomotopyComputationIso A D E P).inv.app M := by
  simp only [scalarKernelHomotopyAugmentation, Quotient.natTransLift_app,
    NatTrans.comp_app, Functor.whiskerRight_app]

lemma scalarKernelHomotopyAugmentation_isIso (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    IsIso ((scalarKernelHomotopyAugmentation D E P).app ((moduleToHomotopy A D).obj M)) := by
  have := kernelDerivedTensorAugmentation_isIso_of_relativeKFlat A D E P M hM
  rw [scalarKernelHomotopyAugmentation_app]
  infer_instance

/-- 係数変更前後の二つの導来作用を比較する共通の計算モデル。 -/
def scalarKernelDerivedBaseChangeModel :
    DerivedModuleCategory A D ⥤ DerivedModuleCategory A' (DGBaseChange φ E) :=
  moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D) ⋙
    scalarModuleExtensionHomotopy φ D ⋙
      kernelHomotopyToDerived A' (DGBaseChange φ D) (DGBaseChange φ E) (scalarKernel φ D E P)

/-- 出力の導来係数変更から共通モデルへの自然な比較。 -/
def scalarKernelDerivedBaseChangeLeft :
    kernelDerivedTensorOnBimodule A D E P ⋙ derivedExtension φ E ⟶
      scalarKernelDerivedBaseChangeModel φ D E P :=
  Functor.whiskerLeft
      (moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D) ⋙
        (kernelTensor A D E P).onHomotopy) (scalarExtensionHomotopyAugmentation φ E) ≫
    (Functor.isoWhiskerLeft
      (moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D))
      (scalarKernelBalancedHomotopyDerivedIso φ D E P)).hom

/-- 入力の導来係数変更後のkernel作用から共通モデルへの自然な比較。 -/
def scalarKernelDerivedBaseChangeRight :
    derivedExtension φ D ⋙
        kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P) ⟶
      scalarKernelDerivedBaseChangeModel φ D E P :=
  Functor.whiskerLeft
    (moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D))
    (Functor.whiskerRight (scalarExtensionHomotopyDerivedIso φ D).inv
        (kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P)) ≫
      Functor.whiskerLeft (scalarModuleExtensionHomotopy φ D)
        (scalarKernelHomotopyAugmentation (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P)))

lemma scalarKernelDerivedBaseChangeLeft_isIso
    (hAug : ∀ M : ModuleCategory A D,
      IsIso ((derivedExtensionAugmentation φ E).app
        ((kernelTensor A D E P).onClosed.obj (moduleCanonicalProjectiveResolution A D M).obj))) :
    IsIso (scalarKernelDerivedBaseChangeLeft φ D E P) := by
  have hb (M : ModuleCategory A D) :
      IsIso ((scalarKernelDerivedBaseChangeLeft φ D E P).app ((moduleToDerived A D).obj M)) := by
    let R := moduleCanonicalProjectiveResolution A D M
    let τ := scalarExtensionHomotopyAugmentation φ E
    let Z := (kernelTensor A D E P).onHomotopy
    let eOut := Z.mapIso (moduleDerivedResolutionComputation A D
        (moduleCanonicalProjectiveResolution A D) M) ≪≫
      (eqToIso (kernelTensor A D E P).onHomotopy_fac).app R.obj
    have hmid : IsIso (τ.app
        (((kernelTensor A D E P).onClosed ⋙ moduleToHomotopy A E).obj R.obj)) :=
      scalarExtensionHomotopyAugmentation_isIso φ E
        ((kernelTensor A D E P).onClosed.obj R.obj) (hAug M)
    have hi : IsIso (τ.app (Z.obj
        ((moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D)).obj
          ((moduleToDerived A D).obj M)))) := by
      rw [← τ.naturality_2 eOut]
      infer_instance
    let := hi
    change IsIso (τ.app _ ≫
      (scalarKernelBalancedHomotopyDerivedIso φ D E P).hom.app
        ((moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D)).obj
          ((moduleToDerived A D).obj M)))
    infer_instance
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  let M := (moduleToDerived A D).objPreimage X
  let e := (moduleToDerived A D).objObjPreimageIso X
  have := hb M
  rw [← (scalarKernelDerivedBaseChangeLeft φ D E P).naturality_1 e]
  infer_instance

lemma scalarKernelDerivedBaseChangeRight_isIso
    (hP' : ∀ M : ModuleCategory A D,
      moduleRelativeKFlat A' (DGBaseChange φ D)
        (rightModule φ D (ForgetEnrichment.to (Complex A)
          (moduleCanonicalProjectiveResolution A D M).obj))) :
    IsIso (scalarKernelDerivedBaseChangeRight φ D E P) := by
  have hb (M : ModuleCategory A D) :
      IsIso ((scalarKernelDerivedBaseChangeRight φ D E P).app ((moduleToDerived A D).obj M)) := by
    let R := moduleCanonicalProjectiveResolution A D M
    let H := scalarModuleExtensionHomotopy φ D
    let τ := scalarKernelHomotopyAugmentation (DGBaseChange φ D) (DGBaseChange φ E)
      (scalarKernel φ D E P)
    let eIn := H.mapIso (moduleDerivedResolutionComputation A D
        (moduleCanonicalProjectiveResolution A D) M) ≪≫
      (eqToIso (scalarModuleExtensionHomotopy_fac φ D)).app R.obj
    have hmid : IsIso (τ.app
        ((moduleExtension φ D ⋙ moduleToHomotopy A' (DGBaseChange φ D)).obj R.obj)) :=
      scalarKernelHomotopyAugmentation_isIso (DGBaseChange φ D) (DGBaseChange φ E)
        (scalarKernel φ D E P) ((moduleExtension φ D).obj R.obj) (hP' M)
    have hi : IsIso (τ.app (H.obj
        ((moduleDerivedResolutionFunctor A D (moduleCanonicalProjectiveResolution A D)).obj
          ((moduleToDerived A D).obj M)))) := by
      rw [← τ.naturality_2 eIn]
      infer_instance
    let := hi
    change IsIso ((kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
        (scalarKernel φ D E P)).map
        ((scalarExtensionHomotopyDerivedIso φ D).inv.app _) ≫ τ.app _)
    infer_instance
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  let M := (moduleToDerived A D).objPreimage X
  let e := (moduleToDerived A D).objObjPreimageIso X
  have := hb M
  rw [← (scalarKernelDerivedBaseChangeRight φ D E P).naturality_1 e]
  infer_instance

/-- モデルの可逆性を明示した、全主導来入力射に自然なdg加群値の係数変更比較。 -/
def scalarKernelDerivedBaseChangeIso
    (hAug : ∀ M : ModuleCategory A D,
      IsIso ((derivedExtensionAugmentation φ E).app
        ((kernelTensor A D E P).onClosed.obj (moduleCanonicalProjectiveResolution A D M).obj)))
    (hP' : ∀ M : ModuleCategory A D,
      moduleRelativeKFlat A' (DGBaseChange φ D)
        (rightModule φ D (ForgetEnrichment.to (Complex A)
          (moduleCanonicalProjectiveResolution A D M).obj))) :
    kernelDerivedTensorOnBimodule A D E P ⋙ derivedExtension φ E ≅
      derivedExtension φ D ⋙
        kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P) := by
  have := scalarKernelDerivedBaseChangeLeft_isIso φ D E P hAug
  have := scalarKernelDerivedBaseChangeRight_isIso φ D E P hP'
  exact asIso (scalarKernelDerivedBaseChangeLeft φ D E P) ≪≫
    (asIso (scalarKernelDerivedBaseChangeRight φ D E P)).symm

lemma scalarKernelDerivedBaseChangeIso_hom_comp_right
    (hAug : ∀ M : ModuleCategory A D,
      IsIso ((derivedExtensionAugmentation φ E).app
        ((kernelTensor A D E P).onClosed.obj (moduleCanonicalProjectiveResolution A D M).obj)))
    (hP' : ∀ M : ModuleCategory A D,
      moduleRelativeKFlat A' (DGBaseChange φ D)
        (rightModule φ D (ForgetEnrichment.to (Complex A)
          (moduleCanonicalProjectiveResolution A D M).obj))) :
    (scalarKernelDerivedBaseChangeIso φ D E P hAug hP').hom ≫
        scalarKernelDerivedBaseChangeRight φ D E P =
      scalarKernelDerivedBaseChangeLeft φ D E P := by
  have := scalarKernelDerivedBaseChangeLeft_isIso φ D E P hAug
  have := scalarKernelDerivedBaseChangeRight_isIso φ D E P hP'
  simp only [scalarKernelDerivedBaseChangeIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    asIso_inv, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- 出力圏の局所Hom条件とhPNから、出力の通常モデルでの係数変更計算を保証する。 -/
lemma scalarKernelOutputAugmentation_isIso
    (hE : localHomKFlat A E)
    (hPN : ∀ (M : ModuleCategory A D) (e : E),
      complexKFlat A (BalancedTensor.obj A D
        (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)
        (P.leftAt e))) (M : ModuleCategory A D) :
    IsIso ((derivedExtensionAugmentation φ E).app
      ((kernelTensor A D E P).onClosed.obj (moduleCanonicalProjectiveResolution A D M).obj)) := by
  apply derivedExtensionAugmentation_isIso_of_objectwiseKFlat φ E _ hE
  intro e
  exact hPN M e

/-- hPN・hP'を保持した、出力dg加群全体の導来係数変更比較。
局所Hom条件hEは出力の増大比較を反転するためにのみ使う。 -/
def scalarKernelDerivedBaseChangeIso_ofKFlatModels
    (hE : localHomKFlat A E)
    (hPN : ∀ (M : ModuleCategory A D) (e : E),
      complexKFlat A (BalancedTensor.obj A D
        (ForgetEnrichment.to (Complex A) (moduleCanonicalProjectiveResolution A D M).obj)
        (P.leftAt e)))
    (hP' : ∀ M : ModuleCategory A D,
      moduleRelativeKFlat A' (DGBaseChange φ D)
        (rightModule φ D (ForgetEnrichment.to (Complex A)
          (moduleCanonicalProjectiveResolution A D M).obj))) :
    kernelDerivedTensorOnBimodule A D E P ⋙ derivedExtension φ E ≅
      derivedExtension φ D ⋙
        kernelDerivedTensorOnBimodule A' (DGBaseChange φ D) (DGBaseChange φ E)
          (scalarKernel φ D E P) :=
  scalarKernelDerivedBaseChangeIso φ D E P
    (scalarKernelOutputAugmentation_isIso φ D E P hE hPN) hP'

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelDerivedComparison

/-! ## ScalarExtensionKernelHomotopyNaturality（旧 SerrePositivity/DifferentialGraded/Morita/ScalarExtensionKernelHomotopyNaturality.lean） -/

/-! # kernel係数変更比較のH⁰におけるkernel射自然性 -/

@[expose] public section ScalarExtensionKernelHomotopyNaturality
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory ScalarExtension
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

lemma scalarKernelBalancedHomotopyIso_app (P : Bimodule A E D)
    (M : ModuleCategory A D) :
    (scalarKernelBalancedHomotopyIso φ D E P).hom.app ((moduleToHomotopy A D).obj M) =
      (moduleToHomotopy A' (DGBaseChange φ E)).map
        (scalarKernelBalancedIso φ D E P (ForgetEnrichment.to (Complex A) M)).hom := by
  simp only [scalarKernelBalancedHomotopyIso, Quotient.natIsoLift_hom,
    Quotient.natTransLift_app, scalarKernelBalancedHomotopyFacIso, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, eqToIso.hom, eqToIso.inv, eqToHom_app,
    scalarKernelBalancedNatIso, NatIso.ofComponents]
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id]

lemma scalarKernelExtensionHomotopy_map_closed {M N : ModuleCategory A D} (g : M ⟶ N) :
    (scalarModuleExtensionHomotopy φ D).map ((moduleToHomotopy A D).map g) =
      (moduleToHomotopy A' (DGBaseChange φ D)).map ((moduleExtension φ D).map g) := rfl

lemma scalarKernelBalancedHomotopyIso_kernel_naturality
    {P Q : BimoduleCategory A E D} (f : P ⟶ Q) :
    Functor.whiskerRight (kernelTensorHomotopyMap A D E f)
        (scalarModuleExtensionHomotopy φ E) ≫
        (scalarKernelBalancedHomotopyIso φ D E (BimoduleCategory.underlying A E D Q)).hom =
      (scalarKernelBalancedHomotopyIso φ D E (BimoduleCategory.underlying A E D P)).hom ≫
        Functor.whiskerLeft (scalarModuleExtensionHomotopy φ D)
          (kernelTensorHomotopyMap A' (DGBaseChange φ D) (DGBaseChange φ E)
            ((scalarKernelFunctor φ D E).map f)) := by
  apply NatTrans.ext
  funext X
  obtain ⟨M⟩ := X
  change (scalarModuleExtensionHomotopy φ E).map
      ((kernelTensorHomotopyMap A D E f).app ((moduleToHomotopy A D).obj M)) ≫
      (scalarKernelBalancedHomotopyIso φ D E (BimoduleCategory.underlying A E D Q)).hom.app
        ((moduleToHomotopy A D).obj M) =
    (scalarKernelBalancedHomotopyIso φ D E (BimoduleCategory.underlying A E D P)).hom.app
        ((moduleToHomotopy A D).obj M) ≫
      (kernelTensorHomotopyMap A' (DGBaseChange φ D) (DGBaseChange φ E)
        ((scalarKernelFunctor φ D E).map f)).app
        ((moduleToHomotopy A' (DGBaseChange φ D)).obj ((moduleExtension φ D).obj M))
  rw [kernelTensorHomotopyMap_app, scalarKernelExtensionHomotopy_map_closed,
    scalarKernelBalancedHomotopyIso_app, scalarKernelBalancedHomotopyIso_app,
    kernelTensorHomotopyMap_app, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp]
  exact congrArg (moduleToHomotopy A' (DGBaseChange φ E)).map
    (scalarKernelBalancedIso_kernel_naturality φ D E f M)

lemma scalarKernelBalancedHomotopyDerivedIso_kernel_naturality
    {P Q : BimoduleCategory A E D} (f : P ⟶ Q) :
    Functor.whiskerRight (kernelTensorHomotopyMap A D E f)
        (moduleExtensionHomotopyToDerived φ E) ≫
        (scalarKernelBalancedHomotopyDerivedIso φ D E (BimoduleCategory.underlying A E D Q)).hom =
      (scalarKernelBalancedHomotopyDerivedIso φ D E (BimoduleCategory.underlying A E D P)).hom ≫
        Functor.whiskerLeft (scalarModuleExtensionHomotopy φ D)
          (Functor.whiskerRight
            (kernelTensorHomotopyMap A' (DGBaseChange φ D) (DGBaseChange φ E)
              ((scalarKernelFunctor φ D E).map f))
            (moduleHomotopyToDerivedClosed A' (DGBaseChange φ E))) := by
  apply NatTrans.ext
  funext X
  simp only [scalarKernelBalancedHomotopyDerivedIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [← Category.assoc]
  erw [(scalarExtensionHomotopyDerivedIso φ E).inv.naturality
    ((kernelTensorHomotopyMap A D E f).app X)]
  simp only [Functor.comp_map, Category.assoc]
  have h := congrArg (moduleHomotopyToDerivedClosed A' (DGBaseChange φ E)).map
    (NatTrans.congr_app (scalarKernelBalancedHomotopyIso_kernel_naturality φ D E f) X)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    CategoryTheory.Functor.map_comp] at h
  exact congrArg (fun k => (scalarExtensionHomotopyDerivedIso φ E).inv.app
    (((kernelTensor A D E (BimoduleCategory.underlying A E D P)).onHomotopy).obj X) ≫ k) h

end SerrePositivity.DifferentialGraded.Morita
end

end ScalarExtensionKernelHomotopyNaturality
