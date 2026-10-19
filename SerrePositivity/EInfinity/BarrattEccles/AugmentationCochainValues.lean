module

public import SerrePositivity.EInfinity.BarrattEccles.AugmentationValues
public import SerrePositivity.EInfinity.BarrattEccles.Degrees

/-!
# 整数コチェインの augmentation の0次成分

概要：Berger–Fresse §1.1 の augmentation の0次成分を係数環 A で計算する。
方針：次数埋め込みの延長の自然性と一点複体の同型を使う。
規約：コチェインの0次と正規化鎖の0次を標準同型で同定する。
使われ方：augmentation の対称群作用、単位と合成の保存則を示す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：整数コチェインの augmentation の0次は正規化鎖の0次の augmentation である（Berger–Fresse §1.1.2）。
方針：extendMap と extendSingleIso の0次成分を計算する。
規約：終域の A[0] の0次を A へ移して比較する。
使われ方：正規化生成元で得た値を複体の射へ移す。 -/
lemma complexAugmentation_zero_apply (n : ℕ) (w : (normalizedChains A n).X 0) :
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
        ((complexAugmentation A n).f 0 ((complexXIso A n 0).inv w)) =
      (normalizedChainContraction A n).hom.f 0 w := by
  change (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
      ((extendSingleIso ComplexShape.embeddingDownNat (𝟙_ (ModuleCat A)) 0 0 rfl).hom.f 0
        ((extendMap (normalizedChainContraction A n).hom ComplexShape.embeddingDownNat).f 0
          ((complexXIso A n 0).inv w))) = _
  rw [extendSingleIso_hom_f,
    extendMap_f (normalizedChainContraction A n).hom ComplexShape.embeddingDownNat
      (i := 0) (i' := 0) rfl]
  simp only [ModuleCat.comp_apply, complexXIso, Iso.inv_hom_id_apply,
    ChainComplex.single₀ObjXSelf, Iso.refl_hom]
  change (normalizedChainContraction A n).hom.f 0
      ((complexXIso A n 0).hom ((complexXIso A n 0).inv w)) = _
  exact congrArg (fun z => (normalizedChainContraction A n).hom.f 0 z)
    (congrArg (fun f => f w) (complexXIso A n 0).inv_hom_id)

/-- 概要：整数コチェインの augmentation は各0単体を1へ送る（Berger–Fresse §1.1.2）。
方針：0次成分の比較と正規化鎖での生成元の公式を使う。
規約：出力の0次を係数環 A と同定する。
使われ方：augmentation の単位保存と部分合成の保存を検証する。 -/
lemma complexAugmentation_generator_zero (n : ℕ) (x : (simplicial n) _⦋0⦌) :
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
        ((complexAugmentation A n).f 0
          ((complexXIso A n 0).inv (normalizedGenerator A n 0 x))) = (1 : A) := by
  rw [complexAugmentation_zero_apply, normalizedAugmentation_generator_zero]

end SerrePositivity.EInfinity.BarrattEccles
