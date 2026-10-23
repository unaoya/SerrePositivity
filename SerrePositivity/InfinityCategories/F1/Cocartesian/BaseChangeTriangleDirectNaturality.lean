module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTransportTriangleDataCoherence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeTriangleLongNaturality

/-!
概要：輸送三角形の直接辺は、元の全 Hom 上で直接の大域自然性と同じ表示正規化の合成。
方針：長辺の両端の作用を厳密に回収し、同じ指定同型を端点の等式で正規化する。
規約：元の直接辺・大域自然性・端点正規化の値を保持する。
使われ方：元の輸送三角形の等式を局所自然性の三角形の等式へ移す。
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

/-- 元の全 Hom 上の長辺輸送の始点は、同じ直接底変換後の分類作用と輸送の合成。 -/
lemma cocartesianBaseChangeTriangleLong_originalHom_source :
    cocartesianBaseChangeTriangleHomComparison l k p q ≫
      ((cocartesianBaseChangeTriangleHomLong l k p q ≫
        cocartesianBaseChangeHomSpanOne (l ⋙ k) p q) ≫
          cocartesianBaseChangeHomTransport (l ⋙ k) p q) =
    (SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).map p q) ≫
      cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (l ⋙ k))).obj q) ≫
          cocartesianBaseChangeHomTransport (l ⋙ k) p q := by
  simp only [← Category.assoc, cocartesianBaseChangeTriangleHomComparison_long,
    cocartesianBaseChangeHomComparison_one]

/-- 元の全 Hom 上の長辺輸送の終点は、元の分類 Hom 作用の直接の底制限。 -/
lemma cocartesianBaseChangeTriangleLong_originalHom_target :
    cocartesianBaseChangeTriangleHomComparison l k p q ≫
      (cocartesianBaseChangeTriangleHomLong l k p q ≫
        cocartesianBaseChangeHomSpanZero (l ⋙ k) p q) =
    cocartesianStraighteningHomInterval p q ≫ intervalDiagramRestriction
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (l ⋙ k)))
      (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom) := by
  simp only [← Category.assoc, cocartesianBaseChangeTriangleHomComparison_long,
    cocartesianBaseChangeHomComparison_zero]

/-- 同じ長辺比較の端点正規化は、元の直接の大域自然性そのものである。 -/
lemma cocartesianBaseChangeTriangleHomLong_transportIso_normalized :
    F2.functorIsoOfEq
      ((cocartesianBaseChangeTriangleHomLong_transportIso l k p q).precomp
        (cocartesianBaseChangeTriangleHomComparison l k p q))
      (cocartesianBaseChangeTriangleLong_originalHom_source l k p q)
      (cocartesianBaseChangeTriangleLong_originalHom_target l k p q) =
    cocartesianBaseChangeHomNaturalityIso (l ⋙ k) p q := by
  exact eq_of_heq ((F2.functorIsoOfEq_heq _ _ _).trans
    (cocartesianBaseChangeTriangleHomLong_transportIso_naturality_heq l k p q))

/-- 同じ直接辺を元の全 Hom に戻すと、直接の大域自然性に同じ表示正規化を作用させた値。 -/
lemma cocartesianBaseChangeTransportTriangleDirectIso_naturality_heq :
    HEq ((cocartesianBaseChangeTransportTriangleDirectIso l k p q).precomp
      (cocartesianBaseChangeTriangleHomComparison l k p q))
      ((cocartesianBaseChangeHomNaturalityIso (l ⋙ k) p q).postcomp
        (cocartesianBaseChangeHomCompositionNormalization l k p q)) := by
  have h := functorIsoOfEq_postcomp_heq_of_eq
    ((cocartesianBaseChangeTriangleHomLong_transportIso l k p q).precomp
      (cocartesianBaseChangeTriangleHomComparison l k p q))
    (cocartesianBaseChangeTriangleLong_originalHom_source l k p q)
    (cocartesianBaseChangeTriangleLong_originalHom_target l k p q)
    (cocartesianBaseChangeHomNaturalityIso (l ⋙ k) p q)
    (cocartesianBaseChangeTriangleHomLong_transportIso_normalized l k p q)
    (cocartesianBaseChangeHomCompositionNormalization l k p q)
  exact (cocartesianBaseChangeTransportTriangleDirectIso_precomp_heq l k p q _).trans h.symm

end SerrePositivity.InfinityCategories
