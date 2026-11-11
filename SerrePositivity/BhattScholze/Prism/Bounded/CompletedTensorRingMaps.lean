module

public import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensor

/-!
# 完備テンソル積の環射と δ 射

## 概要
両脚で δ 構造と両立する環射は、完備テンソル積全体でも δ 射である。
## 方針
既存の δ 射の延長を作り、導来完備化 H⁰ の環としての一意性で指定の環射と同定する。
## 規約
BS 著者版 Corollary 3.12・Proposition 3.13 (2)。標的の p と左生成元の像の導来完備性を明示する。
## 使われ方
Remark 4.19 の底変換の環同型を prism の比較にする。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
open DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime]
variable {A B C T : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing T]
variable [Algebra A B] [Algebra A C] (Q : OrientedPrism p B)

/-- 両脚で一致する完備テンソル積の環射は、完備な標的では一致する。 -/
theorem prismCompletedTensorRingHom_ext
    {k k' : PrismCompletedTensor (A := A) (C := C) Q →+* T}
    (hl : k.comp (prismCompletedTensorLeft Q) = k'.comp (prismCompletedTensorLeft Q))
    (hr : k.comp (prismCompletedTensorRight Q) = k'.comp (prismCompletedTensorRight Q))
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (k' (prismCompletedTensorLeft Q Q.generator))
      (ModuleCat.of T T)) : k = k' := by
  apply pdCompletionRingHom_ext (B ⊗[A] C) p
    ((Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C) Q.generator)
    T (k'.comp (pdCompletionUnit (B ⊗[A] C) p _)) hp hd k k' _ rfl
  apply Algebra.TensorProduct.ringHom_ext
  · exact hl
  · exact hr

variable (D : DeltaStructure p A) (F : DeltaStructure p C)
variable (hQ : D.IsDeltaHom Q.deltaStructure (algebraMap A B))
variable (hF : D.IsDeltaHom F (algebraMap A C))

/-- 概要：両脚が δ 射である環射は完備テンソル積からの δ 射。
方針：δ 射の延長と環射の一意性を接続する。
規約：BS 著者版 Proposition 3.13 (2)。使われ方：底変換の環比較の δ 構造。 -/
theorem prismCompletedTensor_isDeltaHom_of_legs (G : DeltaStructure p T)
    (k : PrismCompletedTensor (A := A) (C := C) Q →+* T)
    (hl : Q.deltaStructure.IsDeltaHom G (k.comp (prismCompletedTensorLeft Q)))
    (hr : F.IsDeltaHom G (k.comp (prismCompletedTensorRight Q)))
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (k (prismCompletedTensorLeft Q Q.generator))
      (ModuleCat.of T T)) :
    (prismCompletedTensorDelta Q D F hQ hF).IsDeltaHom G k := by
  have hs := congrArg k.comp (prismCompletedTensor_square (A := A) (C := C) Q)
  simp only [← RingHom.comp_assoc] at hs
  obtain ⟨k', hk', _⟩ := existsUnique_prismCompletedTensorHom Q D F hQ hF G
    (k.comp (prismCompletedTensorLeft Q)) (k.comp (prismCompletedTensorRight Q))
    hl hr hs hp hd
  have he : k' = k := prismCompletedTensorRingHom_ext Q hk'.2.1 hk'.2.2 hp hd
  exact he ▸ hk'.1

end SerrePositivity.BhattScholze
