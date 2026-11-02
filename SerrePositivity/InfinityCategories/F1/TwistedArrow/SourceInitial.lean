module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.Source
public import SerrePositivity.InfinityCategories.F1.Joins.CosliceTwistedHomEquivalence
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberComparison
public import SerrePositivity.InfinityCategories.Core.ColimitCoconeFamily
public import SerrePositivity.InfinityCategories.Core.IdentityCocone
public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftFibrationPointHomFamily
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomActionComparison

/-!
概要：始点固定の twisted arrow の恒等点は始対象であり、全 Hom による fiber の族は同値。
方針：元の coslice 比較の fiber を主比較に厳密に戻し、全空間の同値と始対象性を移す。
規約：同値は元の cosliceToTwistedArrowSource の作用そのもの。
使われ方：同じ Yoneda 写像の恒等点評価を、始対象からの普遍輸送として検出する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の coslice 比較の実際の fiber 写像は、同じ両端固定の主比較を回収する。 -/
lemma cosliceToTwistedArrowSource_fiber_compare {C : SSet.{u}} (x y : C _⦋0⦌) :
    vertexFiberMap (sliceUnderProjection (SSet.yonedaEquiv.symm x))
        (twistedArrowSourceProjection x) (cosliceToTwistedArrowSource x)
        (cosliceToTwistedArrowSource_projection x) y ≫
      (twistedArrowSourceFiberIso x y).hom = cosliceTwistedHomMap x y := by
  apply vertexFiber_hom_ext (twistedArrowProjection C) (SSet.opObjEquiv.symm x, y)
  rw [Category.assoc, twistedArrowSourceFiberIso_ι, ← Category.assoc,
    vertexFiberMap_ι, Category.assoc, cosliceToTwistedArrowSource_fst,
    cosliceTwistedHomMap_ι]

/-- 元の coslice から始点固定の全空間への比較は、全空間の前合成同値。 -/
lemma cosliceToTwistedArrowSource_isPrecompositionEquivalence
    {C : SSet.{u}} [Quasicategory C] (x : C _⦋0⦌) :
    IsPrecompositionEquivalence (cosliceToTwistedArrowSource x) := by
  apply isPrecompositionEquivalence_of_leftFibration_fibers
    (sliceUnderProjection (SSet.yonedaEquiv.symm x)) (twistedArrowSourceProjection x)
    (cosliceToTwistedArrowSource x) (cosliceToTwistedArrowSource_projection x)
  intro y
  apply (qCatEquivalenceOfIso (twistedArrowSourceFiberIso x y)).isQCatEquivalence.cancel_right
  change IsQCatEquivalence
    (vertexFiberMap (sliceUnderProjection (SSet.yonedaEquiv.symm x))
      (twistedArrowSourceProjection x) (cosliceToTwistedArrowSource x)
      (cosliceToTwistedArrowSource_projection x) y ≫ (twistedArrowSourceFiberIso x y).hom)
  rw [cosliceToTwistedArrowSource_fiber_compare]
  exact cosliceTwistedHomMap_isQCatEquivalence x y

/-- 元の coslice から始点固定の全空間への実際の比較は quasicategory の同値。 -/
lemma cosliceToTwistedArrowSource_isQCatEquivalence
    {C : SSet.{u}} [Quasicategory C] (x : C _⦋0⦌) :
    IsQCatEquivalence (cosliceToTwistedArrowSource x) :=
  (cosliceToTwistedArrowSource_isPrecompositionEquivalence x).isQCatEquivalence

/-- 元の coslice の恒等錐の像として指定する、始点固定の twisted arrow の恒等点。 -/
def twistedArrowSourceIdentity {C : SSet.{u}} (x : C _⦋0⦌) :
    (twistedArrowSource x) _⦋0⦌ :=
  (cosliceToTwistedArrowSource x).app (Opposite.op ⦋0⦌) (cosliceIdentityCone x)

/-- 同じ恒等点の射影は、元の頂点そのもの。 -/
lemma twistedArrowSourceIdentity_projection {C : SSet.{u}} (x : C _⦋0⦌) :
    (twistedArrowSourceProjection x).app (Opposite.op ⦋0⦌) (twistedArrowSourceIdentity x) = x := by
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (cosliceIdentityCone x))
    (cosliceToTwistedArrowSource_projection x)
  exact h.trans (cosliceIdentityCone_projection x)

/-- 元の恒等錐の像は、始点固定の twisted arrow の全空間の始対象。 -/
lemma twistedArrowSourceIdentity_isInitialVertex
    {C : SSet.{u}} [Quasicategory C] (x : C _⦋0⦌) :
    IsInitialVertex (twistedArrowSourceIdentity x) :=
  (cosliceToTwistedArrowSource_isQCatEquivalence x).choose.map_isInitialVertex
    (cosliceIdentityCone_isInitialVertex x)

/-- 同じ恒等点からの底の全左 Hom による fiber の族は同値。 -/
lemma twistedArrowSourceIdentityHomFamily_homotopyEquivalence
    {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌) :
    IsSimplicialHomotopyEquivalence
      (HomotopyLimits.leftFibrationPointHomFamily (twistedArrowSourceProjection x)
        (twistedArrowSourceIdentity x) y) :=
  HomotopyLimits.leftFibrationPointHomFamily_homotopyEquivalence
    (twistedArrowSourceProjection x) (twistedArrowSourceIdentity x) y
    (twistedArrowSourceIdentity_isInitialVertex x)

/-- 同じ恒等点における、全左 Hom パラメーターの実際の輸送作用も同値。 -/
lemma twistedArrowSourceIdentityPointHomAction_isQCatEquivalence
    {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌) :
    IsQCatEquivalence
      (HomotopyLimits.pointHomTransportActionAt (twistedArrowSourceProjection x)
        ((twistedArrowSourceProjection x).app (Opposite.op ⦋0⦌) (twistedArrowSourceIdentity x)) y
        (HomotopyLimits.pointHomSourceVertex
          (twistedArrowSourceProjection x) (twistedArrowSourceIdentity x))) := by
  have h := (twistedArrowSourceIdentityHomFamily_homotopyEquivalence x y).isQCatEquivalence
  exact h.ofFunctorIso (functorIsoOfSimplicialHomotopy
    (HomotopyLimits.pointHomActionComparisonHomotopy
      (twistedArrowSourceProjection x) (twistedArrowSourceIdentity x) y))

/-- 同じ恒等点からの輸送を、元の端点と元の両端固定の Hom の間に正規化する。 -/
def twistedArrowIdentityHomTransport
    {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌) :
    pinchedHomLeft x y ⟶ twistedArrowHomSpace x y :=
  eqToHom (congrArg (fun a ↦ pinchedHomLeft a y)
      (twistedArrowSourceIdentity_projection x).symm) ≫
    HomotopyLimits.pointHomTransportActionAt (twistedArrowSourceProjection x)
      ((twistedArrowSourceProjection x).app (Opposite.op ⦋0⦌) (twistedArrowSourceIdentity x)) y
      (HomotopyLimits.pointHomSourceVertex
        (twistedArrowSourceProjection x) (twistedArrowSourceIdentity x)) ≫
    (twistedArrowSourceFiberIso x y).hom

/-- 恒等点からの実際の全 Hom 輸送は、元の端点を固定した写像空間の同値。 -/
lemma twistedArrowIdentityHomTransport_isQCatEquivalence
    {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌) :
    IsQCatEquivalence (twistedArrowIdentityHomTransport x y) :=
  (qCatEquivalenceOfIso (eqToIso (congrArg (fun a ↦ pinchedHomLeft a y)
    (twistedArrowSourceIdentity_projection x).symm))).isQCatEquivalence.comp
      ((twistedArrowSourceIdentityPointHomAction_isQCatEquivalence x y).comp
        (qCatEquivalenceOfIso (twistedArrowSourceFiberIso x y)).isQCatEquivalence)

end SerrePositivity.InfinityCategories
