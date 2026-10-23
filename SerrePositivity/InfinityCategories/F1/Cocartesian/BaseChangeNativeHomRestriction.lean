module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNativeHomPath
public import SerrePositivity.InfinityCategories.F1.Cocartesian.IsoTransportNativeHomComparison

/-!
概要：全局所結合 Hom 比較を元の全 Hom の二重底変換で制限すると、大域結合 Hom 比較。
方針：coherent Hom 比較の豊穣自然性と、同じ可逆 path の全族の一致を使う。
規約：元の全 Hom 作用・指定比較 path・両端の正規化を保持する。
使われ方：共有頂点での局所自然性と元の大域三角形の指定値の照合。
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

/-- 指定結合同型への関手は、元の core Hom に二回の同じ底変換を作用させる。 -/
lemma cocartesianBaseChangeNativeCoreEnriched_map :
    (cocartesianBaseChangeNativeCoreEnriched l k).map p q =
      (cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q ≫
        (cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q) := by
  exact quasicategoryCoreFunctor.map_comp _ _

/-- 全局所結合 Hom 比較は、元の同じ指定結合同型の Hom 作用を厳密に回収する。 -/
lemma cocartesianIsoTransportNativeHomComparison_baseChange :
    (SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianBaseChangeNativeCoreEnriched l k).map p q) ≫
      cocartesianIsoTransportNativeHomComparison l k p q =
    cocartesianBaseChangeAssociativityHomComparison l k p q := by
  have hn := coherentHomIntervalComparison_enriched_naturality
    (C := CocartesianFibrationCategory (nerve C)) (D := CocartesianIsoTransportCategory A)
    (cocartesianBaseChangeNativeCoreEnriched l k) p q
  have hp : (cocartesianIsoTransportHomPath A).app _
      (coherentNerveVertex ((cocartesianBaseChangeNativeCoreEnriched l k).obj p)) =
      (cocartesianBaseChangeAssociativityHomPath l k).app _ (coherentNerveVertex p) :=
    cocartesianIsoTransportHomPath_native_vertex l k p
  have hq : (cocartesianIsoTransportHomPath A).app _
      (coherentNerveVertex ((cocartesianBaseChangeNativeCoreEnriched l k).obj q)) =
      (cocartesianBaseChangeAssociativityHomPath l k).app _ (coherentNerveVertex q) :=
    cocartesianIsoTransportHomPath_native_vertex l k q
  change (SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianBaseChangeNativeCoreEnriched l k).map p q) ≫
    (coherentHomIntervalComparison
      ((cocartesianBaseChangeNativeCoreEnriched l k).obj p)
      ((cocartesianBaseChangeNativeCoreEnriched l k).obj q) ≫
        intervalMappingPostOfEq (cocartesianIsoTransportHomPath A)
          (coherentNerveVertex ((cocartesianBaseChangeNativeCoreEnriched l k).obj p))
          (coherentNerveVertex ((cocartesianBaseChangeNativeCoreEnriched l k).obj q)) hp hq) = _
  rw [← Category.assoc, ← hn]
  apply intervalMappingUncurry_injective
  rw [intervalMappingPostOfEq_uncurry, intervalMappingPostOfEq_uncurry,
    cocartesianBaseChangeAssociativityHomComparison, intervalMappingPost_uncurry]
  change (intervalMappingUncurry (coherentHomIntervalComparison p q) ≫
    cocartesianBaseChangeNativeInfinityMap l k) ≫ cocartesianIsoTransportHomPath A = _
  rw [Category.assoc, cocartesianBaseChangeNativeInfinityMap_homPath]

/-- 二回の元の底変換作用による制限も、同じ大域結合 Hom 比較そのもの。 -/
lemma cocartesianIsoTransportNativeHomComparison_doubleBaseChange :
    ((SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap l)).map
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
          ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q))) ≫
      cocartesianIsoTransportNativeHomComparison l k p q =
    cocartesianBaseChangeAssociativityHomComparison l k p q := by
  have h := cocartesianIsoTransportNativeHomComparison_baseChange l k p q
  rw [cocartesianBaseChangeNativeCoreEnriched_map, CategoryTheory.Functor.map_comp] at h
  exact h

end SerrePositivity.InfinityCategories
