module
public import SerrePositivity.DifferentialGraded.Morita.KernelAugmentation

/-! # kernel作用の自然な射影解像度モデル

## 概要
通常入力上の導来作用を、選んだ射影解像度とのtensorを値に持つ関手で計算する。

## 方針
H⁰解像度関手の計算同型で値を移し、射を既存のliftによるtensor射と同定する。

## 規約と注意
解像度のliftは通常圏で厳密な関手とはしない。関手法則はH⁰と主導来圏を経由する。
局所Hom K-flat性は不要。

## 使われ方
U16aの作用の合成比較を、通常入力射に自然なモデルから主局所化へ延長する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)
  (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)

/-- H⁰解像度モデルの各値を、通常tensorの主導来像に置き換えた実際の関手。 -/
def kernelResolutionTensorModelFunctor : ModuleCategory A D ⥤ DerivedModuleCategory A E :=
  (moduleResolutionHomotopyFunctor A D R ⋙ kernelHomotopyToDerived A D E P).copyObj
    (fun M => (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj (R M).obj))
    (fun M => kernelTensorHomotopyComputation A D E P (R M).obj)

/-- 主導来作用を通常入力で計算する自然な解像度モデル。 -/
def kernelResolutionTensorModelIso :
    moduleToDerived A D ⋙ kernelResolutionDerivedTensor A D E P R ≅
      kernelResolutionTensorModelFunctor A D E P R :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleDerivedResolutionFunctor_fac A D R)
      (kernelHomotopyToDerived A D E P) ≪≫
    (moduleResolutionHomotopyFunctor A D R ⋙ kernelHomotopyToDerived A D E P).isoCopyObj
      _ (fun M => kernelTensorHomotopyComputation A D E P (R M).obj)

/-- 自然なモデルの射は、選んだliftの通常tensorを局所化した射そのもの。 -/
lemma kernelResolutionTensorModelFunctor_map {M N : ModuleCategory A D} (f : M ⟶ N) :
    (kernelResolutionTensorModelFunctor A D E P R).map f =
      (moduleToDerived A E).map
        ((kernelTensor A D E P).onClosed.map ((R M).lift (R N) f)) := by
  change (kernelTensorHomotopyComputation A D E P (R M).obj).inv ≫
      (kernelHomotopyToDerived A D E P).map
        ((moduleToHomotopy A D).map ((R M).lift (R N) f)) ≫
      (kernelTensorHomotopyComputation A D E P (R N).obj).hom = _
  rw [kernelTensorHomotopyComputation_naturality, Iso.inv_hom_id_assoc]

/-- 右相対K-flatなkernelの作用は、相対K-flat入力を相対K-flat出力に送る。 -/
lemma kernelTensor_relativeKFlat
    (hP : Bimodule.rightRelativeKFlat A E D P) (M : ModuleCategory A D)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) :
    moduleRelativeKFlat A E
      ((kernelTensor A D E P).obj (ForgetEnrichment.to (Complex A) M)) := by
  intro N hN
  have hL : leftModuleAcyclic A D (BalancedTensor.Fubini.leftModule A E D P N) :=
    fun d => hP d N hN
  have h := hM (BalancedTensor.Fubini.leftModule A E D P N) hL
  exact cochainAcyclic_of_iso h
    (BalancedTensor.Fubini.iso A E D P (ForgetEnrichment.to (Complex A) M) N)

end SerrePositivity.DifferentialGraded.Morita
