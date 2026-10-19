module

public import SerrePositivity.EInfinity.NegativeTensor.Comultiplication
public import SerrePositivity.EInfinity.NegativeTensor.Interchange

/-!
# 余積を保つ二入力写像の負次数への移送

概要：Berger–Fresse §1.1.4 の二入力の AW 余積適合性を整数コチェインへ移す。
方針：標準テンソル比較の自然性と四因子交換との可換性を使う。
規約：入力の余積は任意の鎖写像であり、余結合性を追加仮定しない。
使われ方：shuffle と Barratt–Eccles の部分合成の整数模型の余積適合性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.NegativeTensor

open CategoryTheory MonoidalCategory HomologicalComplex

variable {A : Type u} [CommRing A]

/-- 概要：二入力の鎖写像を負次数コチェインのテンソルからの射へ移す（BF §1.1.3）。
方針：テンソル比較の逆に続いて鎖写像の零延長を適用する。
規約：次数埋め込みは n↦−n。
使われ方：一般 shuffle の整数コチェイン模型。 -/
def binaryMap {K L M : ChainComplex (ModuleCat.{u} A) ℕ}
    (f : NatTensor.tensor K L ⟶ M) :
    HomologicalComplex.tensorObj (extend K) (extend L) ⟶ extend M :=
  (comparison K L).inv ≫ extendMap f ComplexShape.embeddingDownNat

private lemma tensor_comp {K L M K' L' M' : CochainComplex (ModuleCat.{u} A) ℤ}
    (f : K ⟶ L) (f' : L ⟶ M) (g : K' ⟶ L') (g' : L' ⟶ M') :
    HomologicalComplex.tensorHom (f ≫ f') (g ≫ g') =
      HomologicalComplex.tensorHom f g ≫ HomologicalComplex.tensorHom f' g' := by
  change ((f ≫ f') ⊗ₘ (g ≫ g')) = (f ⊗ₘ g) ≫ (f' ⊗ₘ g')
  rw [tensorHom_comp_tensorHom]

/-- 概要：二入力写像の負次数への移送は余積適合性を保つ（BF §1.1.4）。
方針：比較の順方向を前置し、自然性と四因子交換の比較で元の等式へ戻す。
規約：余積のテンソルの中間二因子には実際の Koszul 交換を使う。
使われ方：一般 shuffle の AW 余積適合性を整数模型へ移す。 -/
lemma binaryMap_comultiplication {K L M : ChainComplex (ModuleCat.{u} A) ℕ}
    (dK : K ⟶ NatTensor.tensor K K) (dL : L ⟶ NatTensor.tensor L L)
    (dM : M ⟶ NatTensor.tensor M M) (f : NatTensor.tensor K L ⟶ M)
    (h : f ≫ dM = HomologicalComplex.tensorHom dK dL ≫
      (NatTensor.interchange K K L L).hom ≫ HomologicalComplex.tensorHom f f) :
    binaryMap f ≫ comultiplication M dM =
      HomologicalComplex.tensorHom (comultiplication K dK) (comultiplication L dL) ≫
        (SerrePositivity.cochainTensorShuffle (extend K) (extend K) (extend L) (extend L)).hom ≫
        HomologicalComplex.tensorHom (binaryMap f) (binaryMap f) := by
  apply (cancel_epi (comparison K L).hom).1
  simp only [binaryMap, comultiplication, tensor_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← reassoc_of% (comparison_natural dK dL)]
  rw [reassoc_of% (comparison_interchange K K L L)]
  have hc : HomologicalComplex.tensorHom (comparison K L).hom (comparison K L).hom ≫
      HomologicalComplex.tensorHom (comparison K L).inv (comparison K L).inv = 𝟙 _ := by
    change ((comparison K L).hom ⊗ₘ (comparison K L).hom) ≫
      ((comparison K L).inv ⊗ₘ (comparison K L).inv) = _
    rw [tensorHom_comp_tensorHom, Iso.hom_inv_id, tensorHom_id]
    simp
    rfl
  rw [reassoc_of% hc]
  have he := congrArg (fun g => extendMap g ComplexShape.embeddingDownNat) h
  simp only [extendMap_comp] at he
  rw [reassoc_of% he]
  rw [comparison_natural f f]

end SerrePositivity.EInfinity.NegativeTensor
