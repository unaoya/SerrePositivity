module

public import SerrePositivity.InfinityCategories.F1.CocartesianOriginalCellOverNaturalityEndpoints

/-!
概要：同じ共有セルへの既存の cellOver 自然性は元の大域自然性と三角等式を満たす。
方針：端点表示だけを揃えた指定三辺に、同じ over 自然性の三角等式を移す。
規約：共有セルの表示と元の指定同型の値を保持する。
使われ方：二単体の Segal 比較の共有頂点での成分 path の整合。
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

/-- 端点の表示だけを揃えた、同じ共有セルへの元の局所自然性。 -/
def cocartesianOriginalCellOverNaturalityNormalizedIso :
    FunctorIso (cocartesianBaseChangeHomNaturalityIso v p q).sourceMap
      (cocartesianOriginalCellOverNaturalitySecondIso l k v h p q).sourceMap :=
  F2.functorIsoOfEq (cocartesianOriginalCellOverNaturalityIso l k v h p q)
    (cocartesianOriginalCellOverNaturality_source l k v h p q)
    (cocartesianOriginalCellOverNaturality_middle l k v h p q)

/-- 終点の表示だけを揃えた、同じ共有セルでの第二辺。 -/
def cocartesianOriginalCellOverNaturalityNormalizedSecondIso :
    FunctorIso (cocartesianOriginalCellOverNaturalitySecondIso l k v h p q).sourceMap
      (cocartesianBaseChangeHomNaturalityIso v p q).targetMap :=
  F2.functorIsoOfEq (cocartesianOriginalCellOverNaturalitySecondIso l k v h p q) rfl
    (cocartesianOriginalCellOverNaturality_target l k v h p q)

/-- 既存の cellOver 自然性自身と同じ共有セルの大域自然性との三角等式。 -/
def CocartesianOriginalCellOverNaturalityTriangleCommutes : Prop :=
  IsoTriangleCommutes (cocartesianOriginalCellOverNaturalityNormalizedIso l k v h p q)
    (cocartesianOriginalCellOverNaturalityNormalizedSecondIso l k v h p q)
    (cocartesianBaseChangeHomNaturalityIso v p q)

/-- 同じ元の全 Hom 上で、共有セルを指定した既存の自然性自身の三角等式。 -/
lemma cocartesianOriginalCellOverNaturalityTriangleCommutes :
    CocartesianOriginalCellOverNaturalityTriangleCommutes l k v h p q := by
  subst v
  exact cocartesianOriginalOverNaturalityTriangleCommutes l k p q

end SerrePositivity.InfinityCategories
