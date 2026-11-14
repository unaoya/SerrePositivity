module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeUnitStandardData
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeUnitTriangle
public import SerrePositivity.EInfinity.FrameHom.UnitComparisonTransport
/-!
概要：既存の標準導来単位比較自身の弱同値性を同じ全 pinched 族から示す。
方針：元の弱な全要素族と複体屋根族を、同じ単位三角形と指定端点同型で輸送する。
規約：標準単位・実 U・全要素パラメータ・元の頂点表示を保持する。
使われ方：同じ単位 comma 候補の実始対象性の写像空間判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.FrameHom
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 概要：実 U と既存の標準導来単位による比較射自身は任意頂点で弱同値。
方針：同じ二つの弱な全 pinched 族と元の全族三角形を、指定した三つの同型で輸送する。
規約：任意の別の Hom 同値で置き換えない。使われ方：同じ単位 comma 候補の普遍性。 -/
lemma derivedFreeProbeUnitIntervalMap_weak (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) _⦋0⦌)
    (y : (CAlg_R A) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (derivedFreeProbeUnitIntervalMap A x y) := by
  exact unitComparisonTransport_weak (cAlgForgetDerived A)
    (freeProbeRelativeChosenSourceIso A (freeProbeUnitComplex A x))
    (freeProbeUnitTargetIso A y) (freeProbeUnitSourceIso A x)
    (derivedFreeProbeUnitHom A x) (freeProbeRelativeUnitHom A (freeProbeUnitComplex A x))
    (freeProbeRelativeElementPinchedMap A (freeProbeUnitComplex A x)
      (freeProbeUnitCofibrantTarget A y))
    (freeProbeRelativeUnitReference A (freeProbeUnitComplex A x)
      (freeProbeUnitCofibrantTarget A y))
    (freeProbeRelativeElementPinchedMap_weak A (freeProbeUnitComplex A x)
      (freeProbeUnitCofibrantTarget A y))
    (freeProbeRelativeUnitReference_weak A (freeProbeUnitComplex A x)
      (freeProbeUnitCofibrantTarget A y))
    (freeProbeUnitStandard_triangle A x)
    (freeProbeRelativeUnit_forget_family_triangle A (freeProbeUnitComplex A x)
      (freeProbeUnitCofibrantTarget A y))

end SerrePositivity.EInfinity.BarrattEccles
