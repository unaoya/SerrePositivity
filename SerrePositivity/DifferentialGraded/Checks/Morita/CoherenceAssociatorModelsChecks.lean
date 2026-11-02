module
public import SerrePositivity.DifferentialGraded.Morita.CoherenceAssociator
public import Mathlib.Data.ZMod.Basic

/-! # 主導来kernel結合子の同じモデル計算の監査

## 概要
主導来kernel結合子と二つの三因子通常モデルの可換図式を、独立対象宇宙で検査する。

## 方針
任意kernelの結合子の型と、指定K-flat二因子での同型の等式を直接利用する。

## 規約と注意
公開作用全体の結合coherenceは後続の貼合せを要する。この検査だけでU16aを受け入れない。

## 使われ方
U16aの通常モデルから主導来kernelへの結合coherence移送の再現入口。
-/
@[expose] public section
noncomputable section
universe u v w z t
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
open SerrePositivity.DifferentialGraded.Morita
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : Type z) [DGCategory A F] [Small.{u} F]
  (G : Type t) [DGCategory A G] [Small.{u} G]

example (hD : localHomKFlat A D) (hE : localHomKFlat A E)
    (P : Kernel A D E) (Q : Kernel A E F) (R : Kernel A F G) :
    kernelCompose A D E G hD P (kernelCompose A E F G hE Q R) ≅
      kernelCompose A D F G hD (kernelCompose A D E F hD P Q) R :=
  kernelAssociatorIso A D E F G hD hE P Q R

example (hD : localHomKFlat A D) (hE : localHomKFlat A E)
    (P : RightKFlatBimoduleCategory A E D) (Q : RightKFlatBimoduleCategory A F E)
    (R : BimoduleCategory A G F) :
    kernelAssociatorIso A D E F G hD hE ((bimoduleToDerived A E D).obj P.obj)
        ((bimoduleToDerived A F E).obj Q.obj) ((bimoduleToDerived A G F).obj R) ≪≫
      kernelAssociatorNestedModelIso A D E F G hD P Q R =
    kernelAssociatorPairModelIso A D E F G hD hE P Q R ≪≫
      (bimoduleToDerived A G D).mapIso (associatorIso A G F E D
        (BimoduleCategory.underlying A G F R) (BimoduleCategory.underlying A F E Q.obj)
        (BimoduleCategory.underlying A E D P.obj)) := by
  apply Iso.ext
  exact kernelAssociatorIso_model_fac A D E F G hD hE P Q R

example (D : Type v) [DGCategory (ZMod 2) D] [Small.{0} D]
    (E : Type w) [DGCategory (ZMod 2) E] [Small.{0} E] (P : BimoduleCategory (ZMod 2) E D) :
    kernelDerivedTensorOnBimoduleIso (ZMod 2) D E P =
      Iso.refl (kernelDerivedTensorOnBimodule (ZMod 2) D E
        (BimoduleCategory.underlying (ZMod 2) E D P)) :=
  kernelDerivedTensorOnBimoduleIso_refl (ZMod 2) D E P

#print axioms kernelDerivedTensorOnBimoduleIso_refl
#print axioms kernelDerivedTensorFunctor_map_base
#print axioms kernelAssociatorIso
#print axioms kernelAssociatorPairModelIso
#print axioms kernelAssociatorNestedModelIso
#print axioms kernelAssociatorIso_model_fac
#print axioms kernelAssociatorIso_action_model_fac
#print axioms kernelCompositionIso_kFlat_fac
