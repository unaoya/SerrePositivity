module

public import SerrePositivity.InfinityCategories.F1.CocartesianOriginalOverNaturalityImageTriangle

/-!
概要：大域三角形の直接辺は、元の直接自然性の正規化後と同じ両端を持つ。
方針：長辺の端点回収を同じ正規化後に写し、既存の表示変更を順に外す。
規約：元の全 Hom と指定された直接自然性を保持する。
使われ方：正規化前の over 自然性の三角形の端点照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 元の直接自然性を同じ正規化に写した指定辺。 -/
def cocartesianGlobalDirectNaturalityImageIso :=
  (cocartesianBaseChangeHomNaturalityIso (l ⋙ k) p q).postcomp
    (cocartesianBaseChangeHomCompositionNormalization l k p q)

/-- 指定直接辺と元の直接自然性の像は同じ始点を持つ。 -/
lemma cocartesianGlobalDirectNaturalityImage_source :
    (cocartesianGlobalDirectNaturalityImageIso l k p q).sourceMap =
      (cocartesianBaseChangeGlobalTransportDirectIso l k p q).sourceMap := by
  have h := congrArg
    (fun m ↦ m ≫ cocartesianBaseChangeHomCompositionNormalization l k p q)
    (cocartesianBaseChangeTriangleLong_originalHom_source l k p q)
  have hs := (Category.assoc _ _ _).symm.trans h
  have hr := functorIsoOfEq_precomp_sourceMap_of_eq
    ((cocartesianBaseChangeTriangleHomLong_transportIso l k p q).postcomp
      (cocartesianBaseChangeHomCompositionNormalization l k p q))
    (Category.assoc _ _ _) (cocartesianBaseChangeTriangleHom_zero_normalization l k p q)
    (cocartesianBaseChangeTriangleHomComparison l k p q) hs
  exact functorIsoOfEq_sourceMap_of_eq
    (cocartesianBaseChangeOriginalGlobalDirectIso l k p q) rfl
    (cocartesianBaseChangeGlobalTriangle_target l k p q) hr.symm

end SerrePositivity.InfinityCategories
