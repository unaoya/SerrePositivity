module
public import SerrePositivity.HomologicalAlgebra.ExtendedChainHomRows

/-!
概要：指定始域同型で移した行を同じ逆射で評価すると元のcochain成分になる。
方針：元の負次数項同型と指定始域同型の両逆を相殺する。
規約：任意の非有界標的と全次数。既存構成の評価・合成則。
使われ方：HA 1.2.4、IS-W2 B02の実A12の自由生成元への評価。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.HomologicalAlgebra
open CategoryTheory Limits CochainComplex HomComplex HomologicalComplex
variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]

/-- 指定始域同型で移した行の逆射による評価は元の全斉次成分。 -/
theorem extendedChainHomRows_iso_evaluation (L : ChainComplex C ℕ)
    (P H : CochainComplex C ℤ) (e : L.extend ComplexShape.embeddingDownNat ≅ P)
    (q : ℤ) (z : Cochain P H q) (n : ℕ) :
    e.inv.f (-(n : ℤ)) ≫ (negativeChainRowIso L n).hom ≫
      extendedChainHomRows L H q
        ((Cochain.ofHom e.hom).comp z (zero_add q)) n =
      z.v (-(n : ℤ)) (q - n) (by omega) := by
  have he : e.inv.f (-(n : ℤ)) ≫ e.hom.f (-(n : ℤ)) = 𝟙 _ :=
    congrArg (fun t => HomologicalComplex.Hom.f t (-(n : ℤ))) e.inv_hom_id
  dsimp only [extendedChainHomRows]
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, he, Category.id_comp]

end SerrePositivity.HomologicalAlgebra
