module

public import SerrePositivity.EInfinity.Hammock.WordIntersection
public import SerrePositivity.EInfinity.Hammock.WordFactorization
public import Mathlib.Data.Fintype.Card

/-!
# 元の語の写像の列の像を経由する因子分解

概要：任意の元の語の写像を、短い像への全射と元の包含に厳密に分ける。
方針：列の像の部分語への持ち上げと、元の包含の単射性を使う。
規約：像の語の長さは始域以下。元の列の順序と色を保持する。
使われ方：前段階から最大長の交互方向語への射の境界を経由する分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

variable {a b : Word} (f : a ⟶ b)

def imageWord : Word := subword b (columnImage f)

def imageInclusion : imageWord f ⟶ b := subwordInclusion b (columnImage f)

lemma imageInclusion_injective : Function.Injective (imageInclusion f).orderHom :=
  subwordInclusion_injective _ _

lemma imageInclusion_range : Set.range (imageInclusion f).orderHom = Set.range f.orderHom := by
  change Set.range (subwordInclusion b (columnImage f)).orderHom = _
  rw [subwordInclusion_range, coe_columnImage]

def toImage : a ⟶ imageWord f :=
  (factorEmbedding (imageInclusion f) (imageInclusion_injective f) f (by
    rw [imageInclusion_range])).val

lemma toImage_fac : toImage f ≫ imageInclusion f = f :=
  (factorEmbedding (imageInclusion f) (imageInclusion_injective f) f (by
    rw [imageInclusion_range])).property

lemma toImage_surjective : Function.Surjective (toImage f).orderHom := by
  intro j
  have hm : (imageInclusion f).orderHom j ∈ Set.range f.orderHom := by
    rw [← imageInclusion_range f]
    exact ⟨j, rfl⟩
  obtain ⟨i, hi⟩ := hm
  refine ⟨i, imageInclusion_injective f ?_⟩
  have he := congrArg (fun h : a ⟶ b => h.orderHom i) (toImage_fac f)
  exact he.trans hi

lemma imageWord_length_le : (imageWord f).length ≤ a.length := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective _ (toImage_surjective f)

end SerrePositivity.EInfinity.Hammock.Word
