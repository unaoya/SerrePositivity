module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.IsoTransportNativeHomComparison
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityHomSpan

/-!
概要：全局所 Hom の比較の両端評価を、元の始域評価・結合共役の分類作用へ戻す。
方針：元の区間 Hom の普遍的な族へ展開し、同じ path の端点公式を使う。
規約：既存の結合 Hom span と元の全局所 Hom を保持する。
使われ方：同じ結合 Hom 輸送と元の分類作用の照合。
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

/-- 同じ全局所 Hom の比較の普遍的な区間族は、元の coherent Hom 族の後合成。 -/
lemma cocartesianIsoTransportNativeHomComparison_uncurry :
    intervalMappingUncurry (cocartesianIsoTransportNativeHomComparison l k p q) =
    intervalMappingUncurry (coherentHomIntervalComparison
      (show CocartesianIsoTransportCategory A from cocartesianBaseChangeIsoTransportObject l k p)
      (show CocartesianIsoTransportCategory A from cocartesianBaseChangeIsoTransportObject l k q)) ≫
      cocartesianIsoTransportHomPath A := by
  unfold cocartesianIsoTransportNativeHomComparison
  exact intervalMappingPostOfEq_uncurry _ _ _ _ _ _

/-- 同じ結合 span の零評価は、元の始域評価に続く分類作用の全区間族。 -/
lemma cocartesianIsoTransportNativeHomComparison_zero_uncurry :
    intervalMappingUncurry (cocartesianIsoTransportNativeHomComparison l k p q ≫
      cocartesianBaseChangeAssociativityHomSpanZero l k p q) =
    intervalMappingUncurry (coherentHomIntervalComparison
      (show CocartesianIsoTransportCategory A from cocartesianBaseChangeIsoTransportObject l k p)
      (show CocartesianIsoTransportCategory A from cocartesianBaseChangeIsoTransportObject l k q)) ≫
      cocartesianIsoTransportSource A ≫ cocartesianStraighteningCoherentMap A := by
  have h := intervalHomPathEndpoint_uncurry (cocartesianBaseChangeAssociativityHomPath l k) 0
    (coherentNerveVertex p) (coherentNerveVertex q)
    (cocartesianBaseChangeAssociativityHomPath_zero_vertex l k p)
    (cocartesianBaseChangeAssociativityHomPath_zero_vertex l k q)
    (cocartesianIsoTransportNativeHomComparison l k p q)
  rw [cocartesianIsoTransportNativeHomComparison_uncurry, Category.assoc,
    cocartesianIsoTransportHomPath_zero] at h
  exact h

/-- 同じ結合 span の一評価は、元の結合共役に続く分類作用の全区間族。 -/
lemma cocartesianIsoTransportNativeHomComparison_one_uncurry :
    intervalMappingUncurry (cocartesianIsoTransportNativeHomComparison l k p q ≫
      cocartesianBaseChangeAssociativityHomSpanOne l k p q) =
    intervalMappingUncurry (coherentHomIntervalComparison
      (show CocartesianIsoTransportCategory A from cocartesianBaseChangeIsoTransportObject l k p)
      (show CocartesianIsoTransportCategory A from cocartesianBaseChangeIsoTransportObject l k q)) ≫
      cocartesianIsoTransportTarget A ≫ cocartesianStraighteningCoherentMap A := by
  have h := intervalHomPathEndpoint_uncurry (cocartesianBaseChangeAssociativityHomPath l k) 1
    (coherentNerveVertex p) (coherentNerveVertex q)
    (cocartesianBaseChangeAssociativityHomPath_one_vertex l k p)
    (cocartesianBaseChangeAssociativityHomPath_one_vertex l k q)
    (cocartesianIsoTransportNativeHomComparison l k p q)
  rw [cocartesianIsoTransportNativeHomComparison_uncurry, Category.assoc,
    cocartesianIsoTransportHomPath_one] at h
  exact h

end SerrePositivity.InfinityCategories
