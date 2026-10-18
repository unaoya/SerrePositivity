module

public import SerrePositivity.KST.ProExcision.KoszulFiltration

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 切り詰め濾過の自然性

概要：複体の射を有限 Koszul 濾過の射へ延長する準備。
方針：各切り詰めの包含で四角形を比較する。
規約：元の Koszul 冪遷移と同じ複体射を使用する。
使われ方：KST Lemma 4.10 のスペクトル系列を n に関する塔にする。
-/

universe u

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.StupidTruncation

variable {R : Type u} [CommRing R]

/-- 概要：項切り詰めの射は元の複体への包含と可換。
方針：残る項では切り詰めの標準同型、消える項では零性を使う。
規約：平坦性やホモロジーの仮定は不要。使われ方：Koszul 冪遷移の濾過への延長。 -/
theorem truncationMap_comp_inclusion
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (a : ℤ) :
    stupidTruncMap f (ComplexShape.embeddingUpIntGE a) ≫ inclusion L a = inclusion K a ≫ f := by
  apply HomologicalComplex.Hom.ext
  funext q
  by_cases hq : a ≤ q
  · change (stupidTruncMap f (ComplexShape.embeddingUpIntGE a)).f q ≫
      (inclusion L a).f q = (inclusion K a).f q ≫ f.f q
    rw [inclusion_f L a q hq, inclusion_f K a q hq]
    exact stupidTruncMap_stupidTruncXIso_hom f (ComplexShape.embeddingUpIntGE a)
      (show (ComplexShape.embeddingUpIntGE a).f (q - a).toNat = q by simp; omega)
  · exact (above_isZero_X K a q (by omega)).eq_of_src _ _

/-- 概要：切り詰めの包含遷移は複体の射に自然。
方針：標的の元の複体への単射で相殺し、包含の自然性を使う。
規約：二つの下端 a ≥ b を明示。使われ方：KST Lemma 4.10 の濾過の塔。 -/
theorem truncationInclusion_naturality
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)
    (a b : ℤ) (hab : b ≤ a) :
    stupidTruncMap f (ComplexShape.embeddingUpIntGE a) ≫ truncationInclusion L a b hab =
      truncationInclusion K a b hab ≫ stupidTruncMap f (ComplexShape.embeddingUpIntGE b) := by
  have : Mono (inclusion L b) := mono_of_mono_f _ (fun _ ↦ inferInstance)
  apply (cancel_mono (inclusion L b)).mp
  rw [Category.assoc, truncationInclusion_comp_inclusion,
    truncationMap_comp_inclusion, Category.assoc, truncationMap_comp_inclusion,
    ← Category.assoc, truncationInclusion_comp_inclusion]

/-- 概要：複体の射は項濾過の自然変換を与える。
方針：各段で既存の切り詰め写像を使う。規約：p 段の下端は -p。
使われ方：KST Lemma 4.10 の冪遷移と濾過の整合。 -/
def truncationFiltrationMap {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    truncationFiltration K ⟶ truncationFiltration L where
  app p := stupidTruncMap f (ComplexShape.embeddingUpIntGE (-p))
  naturality {p q} h := (truncationInclusion_naturality f (-p) (-q) (neg_le_neg h.le)).symm

/-- 概要：複体を項濾過へ送る関手。
方針：切り詰め写像の恒等・合成の法則を各段に適用する。
規約：値域は整数添字の濾過複体。使われ方：Koszul 冪の塔に濾過を付ける。 -/
def truncationFiltrationFunctor :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ (ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) where
  obj := truncationFiltration
  map := truncationFiltrationMap
  map_id K := by
    apply NatTrans.ext
    funext p
    exact stupidTruncMap_id K _
  map_comp f g := by
    apply NatTrans.ext
    funext p
    exact stupidTruncMap_comp f g _

end SerrePositivity.KST.ProExcision
