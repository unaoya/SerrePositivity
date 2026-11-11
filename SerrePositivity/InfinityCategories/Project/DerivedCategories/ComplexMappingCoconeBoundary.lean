module
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
/-!
概要：mapping cocone の同じ実比較 cochain の微分は、実射影と元の差写像の負合成。
方針：mapping cone の実微分式を次数 -1 のシフトへ移し、元の符号を保持する。
規約：全複体・全 chain map に適用。使われ方：出力分解 Hom の実比較正方形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits CochainComplex HomComplex
/-- mapping cocone の実第二 cochain は、差写像と実第一射影の比較ホモトピー。 -/
lemma complexMappingCocone_snd_boundary {A : Type u} [Category.{v} A] [Preadditive A]
    [HasBinaryBiproducts A] {K L : CochainComplex A ℤ} (d : K ⟶ L) :
    δ (-1) 0 (mappingCocone.snd d) + Cochain.ofHom (mappingCocone.fst d ≫ d) = 0 := by
  rw [Cochain.ofHom_comp]
  dsimp only [mappingCocone.snd, mappingCocone.fst]
  rw [Cochain.δ_leftShift (mappingCone.snd d) (-1) (-1) 0 rfl 1 (by omega)]
  simp only [mappingCone.δ_snd, Cochain.leftShift_neg,
    Cochain.leftShift_comp_zero_cochain, Cochain.ofHom_neg]
  norm_num
/-- 各次数の実 cocone 対象への射は、同じ二射影で厳密に決まる。 -/
lemma complexMappingCocone_X_ext {A : Type u} [Category.{v} A] [Preadditive A]
    [HasBinaryBiproducts A] {K L : CochainComplex A ℤ} (d : K ⟶ L)
    (j : ℤ) {T : A} (f g : T ⟶ (mappingCocone d).X j)
    (h₁ : f ≫ (mappingCocone.fst d).f j = g ≫ (mappingCocone.fst d).f j)
    (h₂ : f ≫ (mappingCocone.snd d).v j (j - 1) (by omega) =
      g ≫ (mappingCocone.snd d).v j (j - 1) (by omega)) : f = g := by
  have decomp (a : T ⟶ (mappingCocone d).X j) :
      a = (a ≫ (mappingCocone.fst d).f j) ≫ (mappingCocone.inl d).v j j (add_zero j) +
        (a ≫ (mappingCocone.snd d).v j (j - 1) (by omega)) ≫
          (mappingCocone.inr d).1.v (j - 1) j (by omega) := by
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add,
      mappingCocone.id_X d j (j - 1) (by omega), Category.comp_id]
  rw [decomp f, decomp g, h₁, h₂]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
