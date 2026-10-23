module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityFactorNaturality
public import SerrePositivity.InfinityCategories.F1.Cocartesian.NativeHomTransportFactorCoherence

/-!
概要：第二面の元の結合因子は、元の全 Hom 上で既存の局所結合 Hom 輸送そのもの。
方針：両者を同じ結合 span の指定因子比較に戻して照合する。
規約：元の全 Hom と既存の指定同型を保持する。
使われ方：元の大域比較三角形と局所自然性の共有頂点での照合。
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

/-- 元の全 Hom 上で、第二面の結合因子は既存の指定局所 Hom 輸送そのもの。 -/
lemma cocartesianBaseChangeSecondTriangleHomAssociativityTransportIso_naturality_heq :
    HEq ((cocartesianBaseChangeSecondTriangleHomAssociativityTransportIso l k p q).precomp
      (cocartesianBaseChangeSecondTriangleHomComparison l k p q))
      ((cocartesianBaseChangeNativeHomTransportIso l k p q).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map
          ((cocartesianBaseChangeNativeCoreEnriched l k).map p q))) := by
  exact HEq.trans
    (cocartesianBaseChangeSecondTriangleHomAssociativityTransportIso_factor_heq l k p q)
    ((cocartesianIsoTransportNativeHomFactorIso_baseChange_heq l k p q).symm.trans
      (cocartesianBaseChangeNativeHomTransportIso_precomp_factor_heq l k p q _).symm)

/-- 同じ中間評価へ正規化しても、元の全 Hom 上の指定結合因子の値を保持する。 -/
lemma cocartesianBaseChangeSecondTriangleHomAssociativityMiddleIso_naturality_heq :
    HEq ((cocartesianBaseChangeSecondTriangleHomAssociativityMiddleIso l k p q).precomp
      (cocartesianBaseChangeSecondTriangleHomComparison l k p q))
      ((cocartesianBaseChangeNativeHomTransportIso l k p q).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map
          ((cocartesianBaseChangeNativeCoreEnriched l k).map p q))) := by
  exact (functorIsoOfEq_precomp_heq
    (cocartesianBaseChangeSecondTriangleHomAssociativityTransportIso l k p q) rfl
    (cocartesianBaseChangeSecondTriangleHom_middle l k p q).symm
    (cocartesianBaseChangeSecondTriangleHomComparison l k p q)).trans
      (cocartesianBaseChangeSecondTriangleHomAssociativityTransportIso_naturality_heq l k p q)

/-- 同じ指定値の照合を、元の二回の底変換 Hom 作用の合成で表す。 -/
lemma cocartesianBaseChangeSecondTriangleHomAssociativityMiddleIso_doubleBaseChange_heq :
    HEq ((cocartesianBaseChangeSecondTriangleHomAssociativityMiddleIso l k p q).precomp
      (cocartesianBaseChangeSecondTriangleHomComparison l k p q))
      ((cocartesianBaseChangeNativeHomTransportIso l k p q).precomp
        ((SSet.uliftFunctor.{u + 1, u}).map
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
          (SSet.uliftFunctor.{u + 1, u}).map
            ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
              ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
              ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q)))) := by
  have h := cocartesianBaseChangeSecondTriangleHomAssociativityMiddleIso_naturality_heq l k p q
  rw [cocartesianBaseChangeNativeCoreEnriched_map, CategoryTheory.Functor.map_comp] at h
  exact h

end SerrePositivity.InfinityCategories
