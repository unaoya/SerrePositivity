module
public import SerrePositivity.HomologicalAlgebra.ExtendedChainHomRows

/-!
概要：零延長した鎖複体の行表示は元の始域複体射の前合成と可換。
方針：同じ負次数項同型と零次cochainの合成成分則を使う。
規約：任意の非有界標的と全次数。既存構成の自然性・合成則。
使われ方：HA 1.2.4、IS-W2 B02の指定重み比較とMoore反転の前合成。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.HomologicalAlgebra
open CategoryTheory Limits CochainComplex HomComplex
variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]

/-- 同じ始域射の前合成は、元の延長項同型で戻した同じ行射の前合成。 -/
theorem extendedChainHomRows_precomp (L K : ChainComplex C ℕ) (H : CochainComplex C ℤ)
    (σ : L.extend ComplexShape.embeddingDownNat ⟶ K.extend ComplexShape.embeddingDownNat)
    (q : ℤ) (z : Cochain (K.extend ComplexShape.embeddingDownNat) H q) (n : ℕ) :
    extendedChainHomRows L H q ((Cochain.ofHom σ).comp z (zero_add q)) n =
      (negativeChainRowIso L n).inv ≫ σ.f (-(n : ℤ)) ≫
        (negativeChainRowIso K n).hom ≫ extendedChainHomRows K H q z n := by
  dsimp only [extendedChainHomRows]
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  simp only [Iso.hom_inv_id_assoc]

end SerrePositivity.HomologicalAlgebra
