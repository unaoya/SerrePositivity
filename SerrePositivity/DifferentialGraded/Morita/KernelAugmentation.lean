module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceIdentity
public import SerrePositivity.DifferentialGraded.Tensor.KFlatComparison

/-! # kernel作用の通常tensorへの増大比較と相対K-flat入力での計算

## 概要
入力解像度の増大射から、主導来作用と通常tensorの自然な比較を構成する。

## 方針
既存のHom mapの評価・H⁰計算同型・増大自然変換を使い、相対K-flat入力で比較を反転する。

## 規約と注意
相対K-flat性を入力右D加群に要求する。Homの局所K-flat性やkernelの射影性は要求しない。

## 使われ方
U16aのkernel合成比較を通常のbimodule結合子へ帰着するための計算API。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor CochainComplex HomComplex
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- 入力Homに対するtensorの作用は各E対象で既存rightHomMapに一致する。 -/
lemma kernelTensor_map_π (M N : RightModule A D) (e : E) :
    (kernelTensor A D E P).map M N ≫
      moduleHomπ A E ((kernelTensor A D E P).obj M) ((kernelTensor A D E P).obj N) e =
      BalancedTensor.rightHomMap A D M N (P.leftAt e) := by
  have h := BimoduleTensor.compose_leftMap_π A E D (RightModule A D) P
    (DGFunctor.id (RightModule A D)) M N e
  change (kernelTensor A D E P).map M N ≫
    moduleHomπ A E ((kernelTensor A D E P).obj M) ((kernelTensor A D E P).obj N) e =
      𝟙 _ ≫ BalancedTensor.rightHomMap A D M N (P.leftAt e) at h
  exact h.trans (Category.id_comp _)

/-- 通常入力射に対する作用を、各値の既存balanced tensor mapで計算する。 -/
lemma kernelTensor_map_eval {M N : ModuleCategory A D} (f : M ⟶ N) (e : E) :
    (moduleEvaluation A E e).map ((kernelTensor A D E P).onClosed.map f) =
      BalancedTensor.rightTensorMap A D (P.leftAt e) f := by
  apply Cochain.ofHom_injective
  rw [moduleEvaluation_cochain]
  change (moduleHomπ A E _ _ e).f 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f ≫
      (kernelTensor A D E P).map _ _)).val = _
  rw [cycleFromUnit_postcomp]
  have h := congrArg (fun k => k.f 0 (cycleFromUnit _
    (ForgetEnrichment.homTo (Complex A) f)).val)
    (kernelTensor_map_π A D E P (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) e)
  exact h.trans (BalancedTensor.rightHomMap_closedElement A D (P.leftAt e) f)

/-- 相対K-flat入力間の準同型を、任意kernelの通常tensor作用が保つ。 -/
lemma kernelTensor_relativeKFlat_quasiIso {M N : ModuleCategory A D}
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M))
    (hN : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) N))
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    moduleQuasiIso A E ((kernelTensor A D E P).onClosed.map f) := by
  intro e
  rw [kernelTensor_map_eval]
  exact BalancedTensor.rightTensor_relativeKFlat_quasiIso A D (P.leftAt e) hM hN f hf

/-- H⁰から主導来値への計算同型は、通常入力の射に自然。 -/
lemma kernelTensorHomotopyComputation_naturality {M N : ModuleCategory A D} (f : M ⟶ N) :
    (kernelHomotopyToDerived A D E P).map ((moduleToHomotopy A D).map f) ≫
        (kernelTensorHomotopyComputation A D E P N).hom =
      (kernelTensorHomotopyComputation A D E P M).hom ≫
        (moduleToDerived A E).map ((kernelTensor A D E P).onClosed.map f) := by
  have h := congrArg (moduleHomotopyToDerivedClosed A E).map
    ((eqToIso (kernelTensor A D E P).onHomotopy_fac).hom.naturality f)
  simp only [CategoryTheory.Functor.map_comp] at h
  dsimp only [kernelTensorHomotopyComputation, Iso.trans_hom, Functor.mapIso_hom,
    kernelHomotopyToDerived, Functor.comp_map]
  rw [← Category.assoc]
  erw [h]
  have hn := (moduleToHomotopyDerivedIso A E).hom.naturality
    ((kernelTensor A D E P).onClosed.map f)
  simp only [Functor.comp_map] at hn
  simp only [Functor.comp_map, Iso.app_hom]
  rw [Category.assoc]
  erw [hn]
  rw [Category.assoc]
  rfl

/-- H⁰計算の成分を、通常入力圏上の自然同型へ束ねる。 -/
def kernelTensorHomotopyComputationIso :
    moduleToHomotopy A D ⋙ kernelHomotopyToDerived A D E P ≅
      (kernelTensor A D E P).onClosed ⋙ moduleToDerived A E :=
  NatIso.ofComponents (kernelTensorHomotopyComputation A D E P)
    (fun f => kernelTensorHomotopyComputation_naturality A D E P f)

/-- 任意指定入力解像度族から通常tensorへの増大比較。 -/
def kernelResolutionTensorAugmentation
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) :
    moduleResolutionHomotopyFunctor A D R ⋙ kernelHomotopyToDerived A D E P ⟶
      (kernelTensor A D E P).onClosed ⋙ moduleToDerived A E :=
  whiskerRight (kernelInputResolutionHomotopyAugmentation A D R)
      (kernelHomotopyToDerived A D E P) ≫
    (kernelTensorHomotopyComputationIso A D E P).hom

/-- 増大比較の成分は、解像度値の計算同型と実際のtensor増大の局所化像。 -/
lemma kernelResolutionTensorAugmentation_app
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M) (M : ModuleCategory A D) :
    (kernelResolutionTensorAugmentation A D E P R).app M =
      (kernelTensorHomotopyComputation A D E P (R M).obj).hom ≫
        (moduleToDerived A E).map ((kernelTensor A D E P).onClosed.map (R M).π) :=
  kernelTensorHomotopyComputation_naturality A D E P (R M).π

/-- 主導来作用から通常tensorへの、通常入力圏上で自然な増大比較。 -/
def kernelDerivedTensorAugmentation :
    moduleToDerived A D ⋙ kernelDerivedTensorOnBimodule A D E P ⟶
      (kernelTensor A D E P).onClosed ⋙ moduleToDerived A E :=
  whiskerRight (moduleDerivedResolutionFunctor_fac A D
      (moduleCanonicalProjectiveResolution A D)).hom (kernelHomotopyToDerived A D E P) ≫
    kernelResolutionTensorAugmentation A D E P (moduleCanonicalProjectiveResolution A D)

/-- 主導来増大比較は標準解像度の計算同型を通して実際のtensor増大に一致する。 -/
lemma kernelDerivedTensorAugmentation_app (M : ModuleCategory A D) :
    (kernelDerivedTensorAugmentation A D E P).app M =
      (kernelResolutionDerivedTensorComputation A D E P
        (moduleCanonicalProjectiveResolution A D) M).hom ≫
        (moduleToDerived A E).map
          ((kernelTensor A D E P).onClosed.map (moduleCanonicalProjectiveResolution A D M).π) := by
  change _ ≫ (kernelResolutionTensorAugmentation A D E P _).app M = _
  rw [kernelResolutionTensorAugmentation_app]
  simp only [kernelResolutionDerivedTensorComputation, Iso.trans_hom, Functor.mapIso_hom,
    whiskerRight_app, moduleDerivedResolutionComputation, Iso.app_hom, Category.assoc]

/-- 相対K-flatな入力では、主導来作用から通常tensorへの増大比較は同型。 -/
lemma kernelDerivedTensorAugmentation_isIso_of_relativeKFlat (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    IsIso ((kernelDerivedTensorAugmentation A D E P).app M) := by
  have hP := moduleHomotopicallyProjective_relativeKFlat A D
    (moduleCanonicalProjectiveResolution A D M).projective
  have hπ := kernelTensor_relativeKFlat_quasiIso A D E P hP hM
    (moduleCanonicalProjectiveResolution A D M).π
    (moduleCanonicalProjectiveResolution A D M).quasiIso
  have := moduleToDerived_inverts A E _ hπ
  rw [kernelDerivedTensorAugmentation_app]
  infer_instance

/-- 相対K-flatな通常入力では、主導来kernel作用を通常tensorの主導来像で計算できる。 -/
def kernelRelativeKFlatComputation (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    (kernelDerivedTensorOnBimodule A D E P).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj M) := by
  have := kernelDerivedTensorAugmentation_isIso_of_relativeKFlat A D E P M hM
  exact asIso ((kernelDerivedTensorAugmentation A D E P).app M)

end SerrePositivity.DifferentialGraded.Morita
