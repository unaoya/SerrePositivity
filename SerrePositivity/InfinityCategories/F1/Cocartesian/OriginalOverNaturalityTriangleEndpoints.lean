module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.GlobalDirectNaturalityEndpoints

/-!
概要：正規化前の元の over 自然性と大域自然性の三辺は同じ端点を持つ。
方針：始点では同型な正規化を消去し、残りは元の底上の制限の合成則を使う。
規約：元の指定三辺と全 Hom を保持する。
使われ方：三角等式を充満忠実な後合成で元の三辺へ反映する。
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

/-- 同じ底上の射による、正規化前の区間 Hom の制限。 -/
def cocartesianBaseChangeHomOverRestriction :=
  intervalDiagramOverPre
    (B := (SSet.uliftFunctor.{u + 1, u}).obj (nerve C)) (X := CatInfinity.{u})
    (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)
    (a := Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (l ⋙ k))))
    (b := Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k)))
    (uliftOverMorphism (cocartesianBaseChangeOverMap l k))

/-- 元の全 Hom 上の既存の over 自然性。 -/
def cocartesianOriginalOverNaturalityIso :=
  (cocartesianLocalHomComparison_overNaturalityIso l k p q).precomp
    (cocartesianSingleBaseChangeHomAction k p q)

/-- 同じ底上の射で制限した元の大域自然性。 -/
def cocartesianOriginalOverNaturalitySecondIso :=
  (cocartesianBaseChangeHomNaturalityIso k p q).postcomp
    (cocartesianBaseChangeHomOverRestriction l k p q)

/-- 正規化前の元の over 自然性と直接の大域自然性の始点は一致する。 -/
lemma cocartesianOriginalOverNaturality_source :
    (cocartesianOriginalOverNaturalityIso l k p q).sourceMap =
      (cocartesianBaseChangeHomNaturalityIso (l ⋙ k) p q).sourceMap := by
  apply (cancel_mono (cocartesianBaseChangeHomCompositionNormalization l k p q)).mp
  have h := (cocartesianLocalHomOverNaturalityOriginalHomImage_endpoints l k p q).1.trans
    (cocartesianGlobalDirectNaturalityImage_source l k p q).symm
  exact (FunctorIso.sourceMap_postcomp (cocartesianOriginalOverNaturalityIso l k p q)
    (cocartesianBaseChangeHomCompositionNormalization l k p q)).symm.trans
      (h.trans (FunctorIso.sourceMap_postcomp
        (cocartesianBaseChangeHomNaturalityIso (l ⋙ k) p q)
        (cocartesianBaseChangeHomCompositionNormalization l k p q)))

/-- 同じ over 自然性の終点は、制限した大域自然性の始点。 -/
lemma cocartesianOriginalOverNaturality_middle :
    (cocartesianOriginalOverNaturalityIso l k p q).targetMap =
      (cocartesianOriginalOverNaturalitySecondIso l k p q).sourceMap := by
  exact (Category.assoc (cocartesianSingleBaseChangeHomAction k p q)
    (cocartesianLocalHomComparison k p q)
    (cocartesianBaseChangeHomOverRestriction l k p q)).symm

/-- 同じ底上の制限の合成則により、二辺と直接辺の終点は一致する。 -/
lemma cocartesianOriginalOverNaturality_target :
    (cocartesianOriginalOverNaturalitySecondIso l k p q).targetMap =
      (cocartesianBaseChangeHomNaturalityIso (l ⋙ k) p q).targetMap := by
  exact (Category.assoc _ _ _).trans
    (congrArg (fun m ↦ cocartesianStraighteningHomInterval p q ≫ m)
      (intervalDiagramOverPre_restriction
        (cocartesianStrictTransportCoherentDiagram p.val.hom)
        (cocartesianStrictTransportCoherentDiagram q.val.hom)
        (uliftOverMorphism (cocartesianBaseChangeOverMap l k))))

end SerrePositivity.InfinityCategories
