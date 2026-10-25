module

public import SerrePositivity.InfinityCategories.F2.Presentable.NativeLeftFibrationPullbackPreservation
public import SerrePositivity.InfinityCategories.F2.Compact.ClassificationTransport
public import SerrePositivity.InfinityCategories.F2.Compact.Preservation

/-!
概要：元の指定全空間を頂点とする引き戻しの分類図式へ、小さい filtered 保存性を移す。
方針：指定全空間と標準引き戻しの底上の同型を分類し、全関手同型で保存性を戻す。
規約：小さい添字の宇宙を保ち、元の頂点を取り替えた結論にしない。
使われ方：元の coslice の分類図式である全共変 Hom の compact 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：三成分の小さい filtered 保存性は元の cartesian な全空間の分類図式へ移る。
方針：標準引き戻しの保存定理と、元の底上の全同型による分類比較を合わせる。
規約：元の宇宙 u の濃度と添字についての保存性を結論する。
使われ方：元の引き戻し coslice の Hom 保存性。 -/
lemma cartesianFibrationClassification_preservesKappaFilteredColimits
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ)
    {T E D B X : SSet.{u + 1}} [Quasicategory X]
    (r₁ : T ⟶ E) (r₂ : T ⟶ D) (p : E ⟶ B) (q : D ⟶ B)
    (hcart : IsPullback r₁ r₂ p q)
    (t : T ⟶ X) (e : E ⟶ X) (d : D ⟶ X) (b : B ⟶ X)
    (ht : r₁ ≫ e = t) (hp : p ≫ b = e) (hq : q ≫ b = d)
    [LeftFibration t] [LeftFibration e] [LeftFibration d] [LeftFibration b] [LeftFibration p]
    (he : Compact.PreservesKappaFilteredColimits.{u, u + 1} μ
      (leftStraighteningInfinityDiagram e))
    (hd : Compact.PreservesKappaFilteredColimits.{u, u + 1} μ
      (leftStraighteningInfinityDiagram d))
    (hb : Compact.PreservesKappaFilteredColimits.{u, u + 1} μ
      (leftStraighteningInfinityDiagram b)) :
    Compact.PreservesKappaFilteredColimits.{u, u + 1} μ (leftStraighteningInfinityDiagram t) := by
  have := relativePullbackProjection_leftFibration p q e d b hp hq
  have hc := leftFibrationPullbackClassification_preservesKappaFilteredColimits
    h p q e d b hp hq he hd hb
  have hi := Compact.leftClassification_overIso t (pullback.fst p q ≫ e)
    hcart.isoPullback (by rw [← Category.assoc, hcart.isoPullback_hom_fst, ht])
  exact hc.of_functorIso hi.symm

end SerrePositivity.InfinityCategories.F2.Presentable
