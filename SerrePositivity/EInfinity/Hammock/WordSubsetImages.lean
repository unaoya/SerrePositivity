module

public import SerrePositivity.EInfinity.Hammock.WordImageFactorization
public import SerrePositivity.EInfinity.Hammock.WordEmbeddingUniqueness

/-!
# 元の列部分集合の包含と単射の像の表示

概要：元の列部分集合の包含はその集合を像とし、任意の単射の像の語と厳密に比較できる。
方針：有限列の像の等式と元の包含の一意性を使う。
規約：部分集合の card と元の語の長さを保持する。
使われ方：境界の有限和表示と proper の交わりの適用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

lemma columnImage_subwordInclusion (c : Word) (s : Finset (Fin c.length)) :
    columnImage (subwordInclusion c s) = s := by
  apply Finset.coe_injective
  rw [coe_columnImage, subwordInclusion_range]

lemma embedding_image_eq {a c : Word} (f : a ⟶ c) (hf : Function.Injective f.orderHom) :
    ∃ h : a = imageWord f, eqToHom h ≫ imageInclusion f = f :=
  embedding_eq_of_range f (imageInclusion f) hf (imageInclusion_injective f)
    (imageInclusion_range f).symm

lemma columnImage_card_of_injective {a c : Word} (f : a ⟶ c)
    (hf : Function.Injective f.orderHom) : (columnImage f).card = a.length := by
  simp only [columnImage, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]

end SerrePositivity.EInfinity.Hammock.Word
