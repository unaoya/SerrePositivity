module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeNaturalWordRows

/-!
# 両行の元の全関手と語の作用の厳密な整合

概要：外側の二列を保つ全語の作用が元の両関手と可換になる。
方針：元の連結関手の自然性と関手の積・定数の合成を使う。
規約：自然同型による置換をせず元の関手の等式を証明する。
使われ方：比較自然変換の区間関手を全語に整合させる。
-/

@[expose] public section
universe u v u' v' uI vI uJ vJ uK vK uL vL uM vM uN vN
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.RelativeNatural
open CategoryTheory

lemma paired_comp_product {I : Type uI} [Category.{vI} I]
    {J : Type uJ} [Category.{vJ} J] {K : Type uK} [Category.{vK} K]
    {L : Type uL} [Category.{vL} L] {M : Type uM} [Category.{vM} M]
    (F : I ⥤ J) (G : I ⥤ K) (H : J ⥤ L) (E : K ⥤ M) :
    F.prod' G ⋙ H.prod E = (F ⋙ H).prod' (G ⋙ E) := rfl

lemma comp_paired {I : Type uI} [Category.{vI} I]
    {J : Type uJ} [Category.{vJ} J] {K : Type uK} [Category.{vK} K]
    {L : Type uL} [Category.{vL} L] (F : I ⥤ J) (G : J ⥤ K) (H : J ⥤ L) :
    F ⋙ G.prod' H = (F ⋙ G).prod' (F ⋙ H) := rfl

lemma comp_constant {I : Type uI} [Category.{vI} I]
    {J : Type uJ} [Category.{vJ} J] {K : Type uK} [Category.{vK} K]
    (F : I ⥤ J) (X : K) : F ⋙ (Functor.const J).obj X = (Functor.const I).obj X := rfl

lemma paired_comp_product_assoc {I : Type uI} [Category.{vI} I]
    {J : Type uJ} [Category.{vJ} J] {K : Type uK} [Category.{vK} K]
    {L : Type uL} [Category.{vL} L] {M : Type uM} [Category.{vM} M]
    {N : Type uN} [Category.{vN} N]
    (F : I ⥤ J) (G : I ⥤ K) (H : J ⥤ L) (E : K ⥤ M) (A : L × M ⥤ N) :
    F.prod' G ⋙ H.prod E ⋙ A = (F ⋙ H).prod' (G ⋙ E) ⋙ A := rfl

lemma comp_paired_assoc {I : Type uI} [Category.{vI} I]
    {J : Type uJ} [Category.{vJ} J] {K : Type uK} [Category.{vK} K]
    {L : Type uL} [Category.{vL} L] {M : Type uM} [Category.{vM} M]
    (F : I ⥤ J) (G : J ⥤ K) (H : J ⥤ L) (A : K × L ⥤ M) :
    F ⋙ G.prod' H ⋙ A = (F ⋙ G).prod' (F ⋙ H) ⋙ A := rfl

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {F G : LocalizerMorphism W V} (η : F.functor ⟶ G.functor)
  {a b : Word} (X Y : C)

lemma beforeFunctor_wordAction (f : a ⟶ b) :
    beforeFunctor η a X Y ⋙ WordAction.functor (wordFunctor.map f) =
      WordAction.functor f ⋙ beforeFunctor η b X Y := by
  change beforeFunctor η a X Y ⋙
    WordAction.functor (Word.appendMap (𝟙 _) (Word.appendMap f (𝟙 _))) = _
  simp only [beforeFunctor, Functor.assoc, ZigzagAppend.functor_naturality,
    paired_comp_product_assoc, WordAction.functor_id, Functor.comp_id,
    Zigzag.Relative.wordAction_functor_eq, comp_paired_assoc, comp_constant]

lemma afterFunctor_wordAction (f : a ⟶ b) :
    afterFunctor η a X Y ⋙ WordAction.functor (wordFunctor.map f) =
      WordAction.functor f ⋙ afterFunctor η b X Y := by
  change afterFunctor η a X Y ⋙
    WordAction.functor (Word.appendMap (𝟙 _) (Word.appendMap f (𝟙 _))) = _
  simp only [afterFunctor, Functor.assoc, ZigzagAppend.functor_naturality,
    paired_comp_product_assoc, WordAction.functor_id, Functor.comp_id,
    Zigzag.Relative.wordAction_functor_eq, comp_paired_assoc, comp_constant]

end SerrePositivity.EInfinity.Hammock.RelativeNatural
