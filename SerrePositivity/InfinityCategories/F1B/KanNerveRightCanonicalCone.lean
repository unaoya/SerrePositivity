module

public import SerrePositivity.InfinityCategories.F1B.KanNerveUnderCanonicalCone
public import SerrePositivity.InfinityCategories.F1B.KanNerveConeNaturality
public import SerrePositivity.InfinityCategories.F1B.KanNerveRightKanShapeIso

/-!
概要：右 Kan の標準錐と通常の comma 上の標準錐を比較する。
方針：Under の uncurry の一致と錐の比較の自然性を合成する。
規約：添字同型の順方向と元の関手を固定する。
使われ方：B5 の指定余単位の局所錐の比較。
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

/-- 概要：通常の右 comma 上で元の関手の構造射から標準錐を作る。
方針：comma の射影を Under の比較へ移し、錐の制限と後合成の自然性を使う。
規約：指定した元の関手と点を保持する。
使われ方：B5 の指定余単位に沿う右 Kan の局所輸送。 -/
def kanClassicalRightKanCanonicalCone : Cone (StructuredArrow.proj c L ⋙ L ⋙ F) :=
  F.mapCone ((kanUnderForgetCone c).whisker (StructuredArrow.toUnder c L))

/-- 概要：native な右 Kan の標準錐は通常の標準錐の nerve と一致する。
方針：comma の射影を Under の比較へ移し、錐の制限と後合成の自然性を使う。
規約：指定した元の関手と点を保持する。
使われ方：B5 の指定余単位に沿う右 Kan の局所輸送。 -/
lemma kanNerveRightKanCanonicalCone :
    joinMap (𝟙 (Δ[0] : SSet.{u})) (kanNerveRightKanShapeIso c L).hom ≫
      (rightKanCanonicalCone (nerveMap L) (nerveMap F) (nerveVertex c)).val =
        (kanNerveCone (kanClassicalRightKanCanonicalCone L F c)).val := by
  have he : (kanNerveRightKanShapeIso c L).hom ≫
      pullback.fst (sliceUnderProjection (nervePoint c)) (nerveMap L) =
        nerveMap (StructuredArrow.toUnder c L) ≫ kanNerveUnderMap c :=
    kanNerveRightKanShapeMap_under L c
  change joinMap (𝟙 (Δ[0] : SSet.{u})) (kanNerveRightKanShapeIso c L).hom ≫
    (sliceUnderUncurry (pullback.fst (sliceUnderProjection (nervePoint c)) (nerveMap L)) ≫
      nerveMap F) = _
  rw [← Category.assoc, ← sliceUnderUncurry_precomp, he, sliceUnderUncurry_precomp,
    kanNerveUnderMap_uncurry, kanNerveCone_whisker, kanNerveCone_mapCone]
  rfl

end SerrePositivity.InfinityCategories.F1B
