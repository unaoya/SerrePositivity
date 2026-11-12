module
public import SerrePositivity.HomologicalAlgebra.NegativeExtendTruncationHom

/-!
概要：アーベル圏での延長・切断 Hom 同値が、元の鎖射の前合成を保つこと。
方針：逆写像は延長射と指定包含の合成であることを使う。
規約：埋め込みの同定を明示し、Dold–Kan の全単体作用素に適用できる。
使われ方：HA 1.2.4、G10 の正規化重みの Hom 比較の自然性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits HomologicalComplex CochainComplex
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- 逆写像は同じ延長射・切断同型・包含の合成。 -/
theorem zeroExtendTruncationHomEquiv_symm (L : ChainComplex C ℕ) (H : CochainComplex C ℤ)
    (f : L ⟶ H.truncLE' (ComplexShape.embeddingUpIntLE 0)) :
    (zeroExtendTruncationHomEquiv L H).symm f =
      extendMap f (ComplexShape.embeddingUpIntLE 0) ≫
        (H.truncLEIso (ComplexShape.embeddingUpIntLE 0)).inv ≫ H.ιTruncLE 0 := rfl

/-- 逆写像と元の鎖射の前合成は可換。 -/
theorem zeroExtendTruncationHomEquiv_symm_comp {L L' : ChainComplex C ℕ}
    (H : CochainComplex C ℤ) (g : L' ⟶ L)
    (f : L ⟶ H.truncLE' (ComplexShape.embeddingUpIntLE 0)) :
    (zeroExtendTruncationHomEquiv L' H).symm (g ≫ f) =
      extendMap g (ComplexShape.embeddingUpIntLE 0) ≫ (zeroExtendTruncationHomEquiv L H).symm f := by
  simp only [zeroExtendTruncationHomEquiv_symm, extendMap_comp, Category.assoc]

/-- 任意の同定済み埋め込みで、同じ前合成を保つ。 -/
theorem extendTruncationHomEquivOfEmbedding_precomp
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
    (he : e = ComplexShape.embeddingUpIntLE 0)
    {L L' : ChainComplex C ℕ} (H : CochainComplex C ℤ) (g : L' ⟶ L)
    (f : L.extend e ⟶ H) :
    extendTruncationHomEquivOfEmbedding e he L' H (extendMap g e ≫ f) =
      g ≫ extendTruncationHomEquivOfEmbedding e he L H f := by
  subst e
  change zeroExtendTruncationHomEquiv L' H _ = g ≫ zeroExtendTruncationHomEquiv L H f
  apply (zeroExtendTruncationHomEquiv L' H).symm.injective
  rw [Equiv.symm_apply_apply, zeroExtendTruncationHomEquiv_symm_comp, Equiv.symm_apply_apply]

/-- 負次数への零延長での Hom 同値は元の全鎖射に自然。 -/
theorem negativeExtendTruncationHomEquiv_precomp {L L' : ChainComplex C ℕ}
    (H : CochainComplex C ℤ) (g : L' ⟶ L)
    (f : L.extend ComplexShape.embeddingDownNat ⟶ H) :
    negativeExtendTruncationHomEquiv L' H (extendMap g ComplexShape.embeddingDownNat ≫ f) =
      g ≫ negativeExtendTruncationHomEquiv L H f :=
  extendTruncationHomEquivOfEmbedding_precomp _ negativeEmbedding_eq H g f

end SerrePositivity.HomologicalAlgebra
