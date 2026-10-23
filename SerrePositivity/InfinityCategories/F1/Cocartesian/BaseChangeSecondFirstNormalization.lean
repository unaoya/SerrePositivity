module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeSecondFirstNaturality
public import SerrePositivity.InfinityCategories.F1.FunctorIsoEndpointProjection

/-!
概要：第二面の二回目の輸送因子を、元の底変換自然性の同じ両端へ正規化する。
方針：同じ最初の面の作用と両射影の厳密な回収則を使う。
規約：元の全 Hom 作用と既存の自然性同型の指定値を保持する。
使われ方：第二辺の二因子を元の局所自然性と同じ端点で貼り合わせる。
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

/-- 同じ輸送因子の始点は、元の二回目の大域自然性を底変換した始点。 -/
lemma cocartesianBaseChangeSecondFirst_originalHom_source :
    cocartesianBaseChangeSecondTriangleHomComparison l k p q ≫
      ((cocartesianBaseChangeSecondTriangleHomFirst l k p q ≫
        cocartesianBaseChangeHomSpanOne l
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) ≫
        cocartesianBaseChangeHomTransport l
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) =
    (SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      ((SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) ≫
        cocartesianStraighteningHomInterval
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p))
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).obj
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) ≫
        cocartesianBaseChangeHomTransport l
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) := by
  have h := congrArg (fun f ↦ f ≫
    (cocartesianBaseChangeHomSpanOne l _ _ ≫ cocartesianBaseChangeHomTransport l _ _))
    (cocartesianBaseChangeSecondTriangleHomComparison_first l k p q)
  simp only [Category.assoc] at h ⊢
  rw [← Category.assoc (cocartesianBaseChangeHomComparison l _ _)
      (cocartesianBaseChangeHomSpanOne l _ _) (cocartesianBaseChangeHomTransport l _ _),
    cocartesianBaseChangeHomComparison_one] at h
  simpa only [Category.assoc] using h

/-- 同じ輸送因子の終点は、元の二回目の大域自然性を底変換した終点。 -/
lemma cocartesianBaseChangeSecondFirst_originalHom_target :
    cocartesianBaseChangeSecondTriangleHomComparison l k p q ≫
      (cocartesianBaseChangeSecondTriangleHomFirst l k p q ≫
        cocartesianBaseChangeHomSpanZero l
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)) =
    (SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      (cocartesianStraighteningHomInterval
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q) ≫
        intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))
          (cocartesianStrictTransportCoherentDiagram
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p).val.hom)
          (cocartesianStrictTransportCoherentDiagram
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q).val.hom)) := by
  have h := congrArg (fun f ↦ f ≫ cocartesianBaseChangeHomSpanZero l _ _)
    (cocartesianBaseChangeSecondTriangleHomComparison_first l k p q)
  simpa only [Category.assoc, cocartesianBaseChangeHomComparison_zero] using h

/-- 同じ端点へ正規化した輸送因子は、元の二回目の大域自然性そのもの。 -/
lemma cocartesianBaseChangeSecondTriangleHomFirstTransportIso_normalized :
    F2.functorIsoOfEq
      ((cocartesianBaseChangeSecondTriangleHomFirstTransportIso l k p q).precomp
        (cocartesianBaseChangeSecondTriangleHomComparison l k p q))
      (cocartesianBaseChangeSecondFirst_originalHom_source l k p q)
      (cocartesianBaseChangeSecondFirst_originalHom_target l k p q) =
    (cocartesianBaseChangeHomNaturalityIso l
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q)) := by
  exact eq_of_heq ((F2.functorIsoOfEq_heq _ _ _).trans
    (cocartesianBaseChangeSecondTriangleHomFirstTransportIso_naturality_heq l k p q))

end SerrePositivity.InfinityCategories
