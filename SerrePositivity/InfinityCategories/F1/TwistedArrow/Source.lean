module

public import SerrePositivity.InfinityCategories.F1.Joins.CosliceTwistedArrowMap
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.TargetFiber
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：始点を固定した twisted arrow 射影と、元の coslice からの底上の比較。
方針：両端射影を始点固定の包含へ引き戻し、元の錐の比較を持ち上げる。
規約：fiber の同型は元の twisted arrow の全空間への包含を保つ。
使われ方：恒等点の始対象性と、同じ Yoneda 写像の全 Hom 上の作用の検出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- twisted arrow の第一変数を元の頂点 x に固定する。 -/
def twistedArrowSourceInclusion {C : SSet.{u}} (x : C _⦋0⦌) : C ⟶ C.op ⊗ C :=
  lift (SSet.const (SSet.opObjEquiv.symm x)) (𝟙 C)

/-- 始点を固定した twisted arrow の全空間。 -/
@[kerodon 03K0]
def twistedArrowSource {C : SSet.{u}} (x : C _⦋0⦌) : SSet.{u} :=
  pullback (twistedArrowProjection C) (twistedArrowSourceInclusion x)

/-- 始点固定の全空間から元の底への射影。 -/
def twistedArrowSourceProjection {C : SSet.{u}} (x : C _⦋0⦌) :
    twistedArrowSource x ⟶ C :=
  pullback.snd (twistedArrowProjection C) (twistedArrowSourceInclusion x)

/-- 始点固定の射影は実際の left fibration。 -/
instance twistedArrowSourceProjection_leftFibration {C : SSet.{u}} [Quasicategory C]
    (x : C _⦋0⦌) : LeftFibration (twistedArrowSourceProjection x) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := twistedArrowProjection C))⟩

/-- 始点固定の全空間も quasicategory。 -/
instance twistedArrowSource_quasicategory {C : SSet.{u}} [Quasicategory C]
    (x : C _⦋0⦌) : Quasicategory (twistedArrowSource x) :=
  quasicategory_of_innerFibration (twistedArrowSourceProjection x)

/-- 始点固定の包含は、指定頂点を元の両端の対へ写す。 -/
lemma twistedArrowSourceInclusion_vertex {C : SSet.{u}} (x y : C _⦋0⦌) :
    (twistedArrowSourceInclusion x).app (Opposite.op ⦋0⦌) y =
      (SSet.opObjEquiv.symm x, y) := by
  change (PinchedHom.constant (SSet.opObjEquiv.symm x) 0, y) = _
  rw [PinchedHom.constant_zero]

/-- 元の coslice の錐の比較は、始点固定の包含を底として持つ。 -/
lemma cosliceTwistedArrowMap_source_over {C : SSet.{u}} (x : C _⦋0⦌) :
    cosliceTwistedArrowMap (SSet.yonedaEquiv.symm x) ≫ twistedArrowProjection C =
    sliceUnderProjection (SSet.yonedaEquiv.symm x) ≫ twistedArrowSourceInclusion x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, twistedArrowProjection_fst, cosliceTwistedArrowMap_left,
      twistedArrowSourceInclusion, lift_fst, SSet.comp_const, Equiv.apply_symm_apply]
  · simp only [Category.assoc, twistedArrowProjection_snd, cosliceTwistedArrowMap_right,
      twistedArrowSourceInclusion, lift_snd, Category.comp_id]

/-- 元の coslice から、始点固定の実際の全空間への比較。 -/
def cosliceToTwistedArrowSource {C : SSet.{u}} (x : C _⦋0⦌) :
    sliceUnder (SSet.yonedaEquiv.symm x) ⟶ twistedArrowSource x :=
  pullback.lift (cosliceTwistedArrowMap (SSet.yonedaEquiv.symm x))
    (sliceUnderProjection (SSet.yonedaEquiv.symm x)) (cosliceTwistedArrowMap_source_over x)

/-- 始点固定の比較は、元の coslice 射影を厳密に保つ。 -/
lemma cosliceToTwistedArrowSource_projection {C : SSet.{u}} (x : C _⦋0⦌) :
    cosliceToTwistedArrowSource x ≫ twistedArrowSourceProjection x =
      sliceUnderProjection (SSet.yonedaEquiv.symm x) :=
  pullback.lift_snd _ _ _

/-- 同じ比較の第一射影は、元の錐の崩壊による比較そのもの。 -/
lemma cosliceToTwistedArrowSource_fst {C : SSet.{u}} (x : C _⦋0⦌) :
    cosliceToTwistedArrowSource x ≫
      pullback.fst (twistedArrowProjection C) (twistedArrowSourceInclusion x) =
    cosliceTwistedArrowMap (SSet.yonedaEquiv.symm x) :=
  pullback.lift_fst _ _ _

/-- 始点固定の fiber は、元の両端固定の twisted arrow 写像空間と厳密に同型。 -/
def twistedArrowSourceFiberIso {C : SSet.{u}} (x y : C _⦋0⦌) :
    vertexFiber (twistedArrowSourceProjection x) y ≅ twistedArrowHomSpace x y :=
  vertexFiberPullbackIso (twistedArrowProjection C) (twistedArrowSourceInclusion x) y ≪≫
    eqToIso (congrArg (vertexFiber (twistedArrowProjection C))
      (twistedArrowSourceInclusion_vertex x y))

/-- 同型は、元の twisted arrow の全空間への包含を厳密に保つ。 -/
lemma twistedArrowSourceFiberIso_ι {C : SSet.{u}} (x y : C _⦋0⦌) :
    (twistedArrowSourceFiberIso x y).hom ≫ vertexFiberι (twistedArrowProjection C)
      (SSet.opObjEquiv.symm x, y) =
    vertexFiberι (twistedArrowSourceProjection x) y ≫
      pullback.fst (twistedArrowProjection C) (twistedArrowSourceInclusion x) := by
  dsimp only [twistedArrowSourceFiberIso, Iso.trans_hom, eqToIso.hom]
  rw [Category.assoc, vertexFiberTransport_ι _ (twistedArrowSourceInclusion_vertex x y),
    vertexFiberPullbackIso_hom_ι]
  rfl

end SerrePositivity.InfinityCategories
