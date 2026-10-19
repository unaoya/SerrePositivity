module

public import SerrePositivity.InfinityCategories.F1B.KanNerveOverCanonicalCocone
public import SerrePositivity.InfinityCategories.F1B.KanNerveLeftKanShapeIso

/-!
概要：左 Kan の標準余錐と通常の comma 上の標準余錐を同定する。
方針：Over の標準余錐の表示を添字の制限と関手の像で移す。
規約：元の指定関手と頂点を保持する。
使われ方：B5 の指定単位の左 Kan 局所余錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {K C D : Type u} [Category.{u} K] [Category.{u} C] [Category.{u} D]
  (L : K ⥤ C) (F : C ⥤ D) (c : C)

/-- 概要：通常の左 comma 上で元の関手の構造射から標準余錐を作る。
方針：Over の uncurry の一致と余錐の自然性を合成する。
規約：元の指定関手と点を保持する厳密な等式。
使われ方：B5 の指定単位に沿う左 Kan の局所輸送。 -/
def kanClassicalLeftKanCanonicalCocone : Cocone (CostructuredArrow.proj L c ⋙ L ⋙ F) :=
  F.mapCocone ((kanOverForgetCocone c).whisker (CostructuredArrow.toOver L c))

/-- 概要：native な左 Kan の標準余錐は通常の標準余錐の nerve と一致する。
方針：Over の uncurry の一致と余錐の自然性を合成する。
規約：元の指定関手と点を保持する厳密な等式。
使われ方：B5 の指定単位に沿う左 Kan の局所輸送。 -/
lemma kanNerveLeftKanCanonicalCocone :
    joinMap (kanNerveLeftKanShapeIso L c).hom (𝟙 (Δ[0] : SSet.{u})) ≫
      (leftKanCanonicalCocone (nerveMap L) (nerveMap F) (nerveVertex c)).val =
        (kanNerveCoconeEquiv (kanClassicalLeftKanCanonicalCocone L F c)).val := by
  have he : (kanNerveLeftKanShapeIso L c).hom ≫
      pullback.snd (nerveMap L) (sliceOverProjection (nervePoint c)) =
        nerveMap (CostructuredArrow.toOver L c) ≫ (kanNerveOverIso c).hom :=
    kanNerveLeftKanShapeMap_over L c
  change joinMap (kanNerveLeftKanShapeIso L c).hom (𝟙 (Δ[0] : SSet.{u})) ≫
    (sliceOverUncurry (pullback.snd (nerveMap L) (sliceOverProjection (nervePoint c))) ≫
      nerveMap F) = _
  rw [← Category.assoc, ← sliceOverUncurry_precomp, he, sliceOverUncurry_precomp,
    kanNerveOverIso_uncurry, kanNerveCocone_whisker, kanNerveCocone_mapCocone]
  rfl

end SerrePositivity.InfinityCategories.F1B
