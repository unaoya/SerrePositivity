module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberValue
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedRightIntervalIdentity

/-!
概要：既存の pointed fiber の値比較の逆を、同じ右 Hom の恒等点輸送で表示する。
方針：値・左右区間比較の同値の両逆を消去し、coslice 全体の恒等輸送へ戻す。
規約：元の値比較の射を変更しない。使われ方：native な余錐輸送と単位表現の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の値の右 Hom 表示から、同じ恒等点の区間輸送で pointed fiber へ戻す。 -/
def pointedValueRightComparison (s : SpaceInfinity.{u} _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject s).obj ⟶
      vertexFiber pointedSpaceProjection s :=
  (pointSpaceRightMappingEquivalenceAt s).inv ≫
    pinchedHomToIntervalMappingSpace pointSpaceVertex s ≫ pointedRightIntervalEvaluate s

/-- 元の標準頂点では、この右 Hom の比較は F1 の指定比較そのもの。 -/
lemma pointedValueRightComparison_standard (K : KanObject.{u}) :
    pointedValueRightComparison (spaceInfinityVertex K) = pointedRightFiberComparison K := rfl

/-- 既存の値比較の後で右 Hom の恒等点輸送を行うと、元の fiber 全体を回収する。 -/
def pointedValueRightComparison_unitIso (s : SpaceInfinity.{u} _⦋0⦌) :
    FunctorIso ((pointedSpaceFiberValueEquivalence s).hom ≫ pointedValueRightComparison s)
      (𝟙 (vertexFiber pointedSpaceProjection s)) := by
  let i := (pointedSpaceFiberPinchedLeftIso s).hom
  let l := (pinchedHomLeftToIntervalMappingSpace_isQCatEquivalence pointSpaceVertex s).choose
  let r := (pinchedHomToIntervalMappingSpace_isQCatEquivalence pointSpaceVertex s).choose
  let e := pointSpaceRightMappingEquivalenceAt s
  let v := pointedRightIntervalEvaluate s
  have he : FunctorIso ((i ≫ l.hom ≫ r.inv ≫ e.hom) ≫ (e.inv ≫ r.hom ≫ v))
      (i ≫ l.hom ≫ r.inv ≫ r.hom ≫ v) := by
    simpa only [Category.assoc, Category.comp_id] using
      ((e.homInvIso.precomp (i ≫ l.hom ≫ r.inv)).postcomp (r.hom ≫ v))
  have hr : FunctorIso (i ≫ l.hom ≫ r.inv ≫ r.hom ≫ v) (i ≫ l.hom ≫ v) := by
    simpa only [Category.assoc, Category.comp_id] using
      ((r.invHomIso.precomp (i ≫ l.hom)).postcomp v)
  have hi : i ≫ l.hom = cosliceFiberToIntervalMappingSpace pointSpaceVertex s := by
    change (cosliceFiberPinchedLeftIso pointSpaceVertex s).hom ≫
      pinchedHomLeftToIntervalMappingSpace pointSpaceVertex s = _
    rw [pinchedHomLeftToIntervalMappingSpace, Iso.hom_inv_id_assoc]
  have h := he ≪≫ hr
  change FunctorIso ((pointedSpaceFiberValueEquivalence s).hom ≫ pointedValueRightComparison s)
    ((i ≫ l.hom) ≫ v) at h
  rw [hi] at h
  exact h ≪≫ pointedRightIntervalEvaluate_cosliceIso s

/-- 同じ二射の逆順の合成も、元の値全体上の恒等射と同型。 -/
def pointedValueRightComparison_counitIso (s : SpaceInfinity.{u} _⦋0⦌) :
    FunctorIso (pointedValueRightComparison s ≫ (pointedSpaceFiberValueEquivalence s).hom)
      (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject s).obj)) := by
  let e := pointedSpaceFiberValueEquivalence s
  let r := pointedValueRightComparison s
  have hi : FunctorIso e.inv r := by
    have a := ((pointedValueRightComparison_unitIso s).precomp e.inv).symm
    have b := e.invHomIso.postcomp r
    have b' : FunctorIso (e.inv ≫ e.hom ≫ r) r := by
      simpa only [Category.assoc, Category.id_comp] using b
    have a' : FunctorIso e.inv (e.inv ≫ e.hom ≫ r) := by
      simpa only [Category.assoc, Category.comp_id] using a
    exact a' ≪≫ b'
  exact (hi.postcomp e.hom).symm ≪≫ e.invHomIso

/-- 右 Hom の同じ恒等点輸送は、既存の値比較を逆射に持つ明示的な同値。 -/
def pointedValueRightEquivalence (s : SpaceInfinity.{u} _⦋0⦌) :
    QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj (spaceInfinityObject s).obj)
      (vertexFiber pointedSpaceProjection s) where
  hom := pointedValueRightComparison s
  inv := (pointedSpaceFiberValueEquivalence s).hom
  homInvIso := pointedValueRightComparison_counitIso s
  invHomIso := pointedValueRightComparison_unitIso s

end SerrePositivity.InfinityCategories.HomotopyLimits
