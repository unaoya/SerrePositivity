module

public import SerrePositivity.HomologicalAlgebra.Complexes.NegativeTensor.Comultiplication
public import SerrePositivity.HomologicalAlgebra.Complexes.NegativeTensor.Interchange

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

namespace SerrePositivity.NegativeTensor

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable {A : Type u} [CommRing A]

/-- 概要：二入力の鎖写像を負次数コチェインのテンソルからの射へ移す（BF §1.1.3）。
方針：テンソル比較の逆に続いて鎖写像の零延長を適用する。
規約：次数埋め込みは n↦−n。
使われ方：一般 shuffle の整数コチェイン模型。 -/
def binaryMap {K L M : ChainComplex (ModuleCat.{u} A) ℕ}
    (f : _root_.SerrePositivity.NatTensor.tensor K L ⟶ M) :
    HomologicalComplex.tensorObj (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L) ⟶ _root_.SerrePositivity.NegativeTensor.extend M :=
  (_root_.SerrePositivity.NegativeTensor.comparison K L).inv ≫ extendMap f ComplexShape.embeddingDownNat

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
    (dK : K ⟶ _root_.SerrePositivity.NatTensor.tensor K K) (dL : L ⟶ _root_.SerrePositivity.NatTensor.tensor L L)
    (dM : M ⟶ _root_.SerrePositivity.NatTensor.tensor M M) (f : _root_.SerrePositivity.NatTensor.tensor K L ⟶ M)
    (h : f ≫ dM = HomologicalComplex.tensorHom dK dL ≫
      (_root_.SerrePositivity.NatTensor.interchange K K L L).hom ≫ HomologicalComplex.tensorHom f f) :
    _root_.SerrePositivity.NegativeTensor.binaryMap f ≫ _root_.SerrePositivity.NegativeTensor.comultiplication M dM =
      HomologicalComplex.tensorHom (_root_.SerrePositivity.NegativeTensor.comultiplication K dK) (_root_.SerrePositivity.NegativeTensor.comultiplication L dL) ≫
        (SerrePositivity.cochainTensorShuffle (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L) (_root_.SerrePositivity.NegativeTensor.extend L)).hom ≫
        HomologicalComplex.tensorHom (_root_.SerrePositivity.NegativeTensor.binaryMap f) (_root_.SerrePositivity.NegativeTensor.binaryMap f) := by
  apply (cancel_epi (_root_.SerrePositivity.NegativeTensor.comparison K L).hom).1
  simp only [_root_.SerrePositivity.NegativeTensor.binaryMap, _root_.SerrePositivity.NegativeTensor.comultiplication, _root_.SerrePositivity.NegativeTensor.tensor_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← reassoc_of% (_root_.SerrePositivity.NegativeTensor.comparison_natural dK dL)]
  rw [reassoc_of% (_root_.SerrePositivity.NegativeTensor.comparison_interchange K K L L)]
  have hc : HomologicalComplex.tensorHom (_root_.SerrePositivity.NegativeTensor.comparison K L).hom (_root_.SerrePositivity.NegativeTensor.comparison K L).hom ≫
      HomologicalComplex.tensorHom (_root_.SerrePositivity.NegativeTensor.comparison K L).inv (_root_.SerrePositivity.NegativeTensor.comparison K L).inv = 𝟙 _ := by
    change ((_root_.SerrePositivity.NegativeTensor.comparison K L).hom ⊗ₘ (_root_.SerrePositivity.NegativeTensor.comparison K L).hom) ≫
      ((_root_.SerrePositivity.NegativeTensor.comparison K L).inv ⊗ₘ (_root_.SerrePositivity.NegativeTensor.comparison K L).inv) = _
    rw [tensorHom_comp_tensorHom, Iso.hom_inv_id, tensorHom_id]
    simp
    rfl
  rw [reassoc_of% hc]
  have he := congrArg (fun g => extendMap g ComplexShape.embeddingDownNat) h
  simp only [extendMap_comp] at he
  rw [reassoc_of% he]
  rw [_root_.SerrePositivity.NegativeTensor.comparison_natural f f]

end SerrePositivity.NegativeTensor
