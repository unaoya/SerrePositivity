module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.OriginalOverNaturalityTriangle
public import SerrePositivity.InfinityCategories.F1.Cocartesian.CellOverNaturality

/-!
概要：同じ共有セルの表示を指定した元の三辺の端点を照合する。
方針：合成セルの等式を消去し、既存の over 自然性の端点照合を回収する。
規約：元の指定 cellOver 自然性と元の全 Hom を保持する。
使われ方：共有頂点での二つの成分 path の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (v : A ⥤ C) (h : l ⋙ k = v)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 元の全 Hom 上の、指定共有セルへの既存の局所自然性。 -/
def cocartesianOriginalCellOverNaturalityIso :=
  (cocartesianLocalHomComparison_cellOverNaturalityIso l k v h p q).precomp
    (cocartesianSingleBaseChangeHomAction k p q)

/-- 同じ指定共有セルへ制限した元の大域自然性。 -/
def cocartesianOriginalCellOverNaturalitySecondIso :=
  (cocartesianBaseChangeHomNaturalityIso k p q).postcomp
    (intervalDiagramOverPre
      (B := (SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) (X := CatInfinity.{u})
      (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom)
      (a := Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap v)))
      (b := Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k)))
      (uliftOverMorphism (cocartesianCellOverMap l k v h)))

/-- 元の cellOver 自然性と同じ共有セルの大域自然性は同じ始点を持つ。 -/
lemma cocartesianOriginalCellOverNaturality_source :
    (cocartesianOriginalCellOverNaturalityIso l k v h p q).sourceMap =
      (cocartesianBaseChangeHomNaturalityIso v p q).sourceMap := by
  subst v
  exact cocartesianOriginalOverNaturality_source l k p q

/-- 元の cellOver 自然性の終点は同じ第二辺の始点。 -/
lemma cocartesianOriginalCellOverNaturality_middle :
    (cocartesianOriginalCellOverNaturalityIso l k v h p q).targetMap =
      (cocartesianOriginalCellOverNaturalitySecondIso l k v h p q).sourceMap := by
  subst v
  exact cocartesianOriginalOverNaturality_middle l k p q

/-- 同じ共有セルへ制限した大域自然性は同じ直接辺の終点を持つ。 -/
lemma cocartesianOriginalCellOverNaturality_target :
    (cocartesianOriginalCellOverNaturalitySecondIso l k v h p q).targetMap =
      (cocartesianBaseChangeHomNaturalityIso v p q).targetMap := by
  subst v
  exact cocartesianOriginalOverNaturality_target l k p q

end SerrePositivity.InfinityCategories
