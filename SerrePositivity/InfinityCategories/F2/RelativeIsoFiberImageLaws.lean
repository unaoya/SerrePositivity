module

public import SerrePositivity.InfinityCategories.F2.RelativeIsoFiberImage

/-!
概要：指定相対同型の fiber 像は恒等・合成・反転の指定値を保つ。
方針：両端の正規化の中間項を消し、ホモトピー圏の関手性を使う。
規約：同型を選び直さない。使われ方：左右三角形からの元の可換同型の fiber 表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
private lemma isoFiberNormalize_refl {C : Type u} [Category.{u} C]
    {a a' : C} (ha : a = a') :
    (eqToIso ha).symm ≪≫ Iso.refl a ≪≫ eqToIso ha = Iso.refl a' := by
  cases ha
  simp

private lemma isoFiberNormalize_trans {C : Type u} [Category.{u} C]
    {a b c a' b' c' : C} (e : a ≅ b) (f : b ≅ c)
    (ha : a = a') (hb : b = b') (hc : c = c') :
    (eqToIso ha).symm ≪≫ (e ≪≫ f) ≪≫ eqToIso hc =
      ((eqToIso ha).symm ≪≫ e ≪≫ eqToIso hb) ≪≫
        ((eqToIso hb).symm ≪≫ f ≪≫ eqToIso hc) := by
  cases ha
  cases hb
  cases hc
  simp

private lemma isoFiberNormalize_symm {C : Type u} [Category.{u} C]
    {a b a' b' : C} (e : a ≅ b) (ha : a = a') (hb : b = b') :
    (eqToIso hb).symm ≪≫ e.symm ≪≫ eqToIso ha =
      ((eqToIso ha).symm ≪≫ e ≪≫ eqToIso hb).symm := by
  cases ha
  cases hb
  simp

variable {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
  {f g h : A ⟶ E} (hf : f ≫ p = a) (hg : g ≫ p = a) (hh : h ≫ p = a) (b : B _⦋0⦌)

/-- 恒等相対同型の fiber 像は元の fiber 射の恒等関手同型。 -/
lemma relativeIsoFiberImage_refl :
    relativeIsoFiberImage p a hf hf (Iso.refl _) b = Iso.refl _ := by
  unfold relativeIsoFiberImage VertexIso.map
  rw [Functor.mapIso_refl]
  exact isoFiberNormalize_refl _

/-- 元の指定相対同型の合成の fiber 像は元の二つの指定像の合成。 -/
lemma relativeIsoFiberImage_trans
    (e : VertexIso (relativeFunctorVertex p a f hf) (relativeFunctorVertex p a g hg))
    (e' : VertexIso (relativeFunctorVertex p a g hg) (relativeFunctorVertex p a h hh)) :
    relativeIsoFiberImage p a hf hh (e ≪≫ e') b =
      relativeIsoFiberImage p a hf hg e b ≪≫ relativeIsoFiberImage p a hg hh e' b := by
  unfold relativeIsoFiberImage VertexIso.map
  rw [Functor.mapIso_trans]
  exact isoFiberNormalize_trans _ _ _ _ _

/-- 元の指定相対同型の反転の fiber 像は同じ指定像の反転。 -/
lemma relativeIsoFiberImage_symm
    (e : VertexIso (relativeFunctorVertex p a f hf) (relativeFunctorVertex p a g hg)) :
    relativeIsoFiberImage p a hg hf e.symm b = (relativeIsoFiberImage p a hf hg e b).symm := by
  unfold relativeIsoFiberImage VertexIso.map
  rw [Functor.mapIso_symm]
  exact isoFiberNormalize_symm _ _ _

end SerrePositivity.InfinityCategories.F2
