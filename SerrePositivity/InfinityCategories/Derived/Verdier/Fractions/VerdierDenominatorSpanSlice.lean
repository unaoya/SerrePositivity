module

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierDenominatorSpanFamily
public import SerrePositivity.KST.LocalizingInvariants.SliceOverCoproduct
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullRestrictionPullback

/-!
概要：実分母・次辺の全空間を、二終点上の単一の marked slice と厳密に同定する。
方針：二図式の実 slice の引き戻しを、同じ実分母条件へ制限して貼り合わせる。
規約：同型は分母射影と実次辺射影を全単体で保持する。
使われ方：元の固定端点 span への比較を、slice と全錐族の比較へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の順序を保持した二終点の固定図式。 -/
def spanTwoPointDiagram {X : SSet.{u}} (x y : X _⦋0⦌) :
    (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X :=
  coprod.desc (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y)

/-- 二終点上の実 slice の、左脚が元の分母である全部分複体。 -/
def verdierDenominatorSpanSlice {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : (sliceOver (spanTwoPointDiagram x y)).Subcomplex :=
  fullSubcomplexOnVertices _ (fun v =>
    (roofPointSliceVertexEdge (SSet.yonedaEquiv.symm x)
      ((sliceOverCoproductLeft (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y)).app
        (Opposite.op ⦋0⦌) v)).edge ∈ weakEquivalences i)

instance verdierDenominatorSpanSlice_quasicategory {A B : StableCategory.{u}}
    (i : ExactMap A B) (x y : B.obj _⦋0⦌) :
    Quasicategory (verdierDenominatorSpanSlice i x y : SSet.{u}) := by
  dsimp only [verdierDenominatorSpanSlice]
  infer_instance

/-- 同じ単一の実錐から、元の実分母を回収する。 -/
def verdierDenominatorSpanSliceLeft {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : (verdierDenominatorSpanSlice i x y : SSet.{u}) ⟶
      (verdierDenominatorOver i x : SSet.{u}) :=
  fullSubcomplexLift _ ((verdierDenominatorSpanSlice i x y).ι ≫
    sliceOverCoproductLeft (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y))
      (fun v => fullSubcomplexOnVertices_vertex v)

/-- 同じ単一の実錐から、元の実次辺を回収する。 -/
def verdierDenominatorSpanSliceRight {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : (verdierDenominatorSpanSlice i x y : SSet.{u}) ⟶
      sliceOver (SSet.yonedaEquiv.symm y) :=
  (verdierDenominatorSpanSlice i x y).ι ≫
    sliceOverCoproductRight (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y)

lemma verdierDenominatorSpanSliceLeft_ι {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : verdierDenominatorSpanSliceLeft i x y ≫
      (verdierDenominatorOver i x).ι = (verdierDenominatorSpanSlice i x y).ι ≫
        sliceOverCoproductLeft (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y) :=
  fullSubcomplexLift_ι _ _ _

/-- 分母条件へ制限しても、元の二つの実始域上の引き戻しを保持する。 -/
lemma isPullback_verdierDenominatorSpanSlice {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) :
    IsPullback (verdierDenominatorSpanSliceRight i x y) (verdierDenominatorSpanSliceLeft i x y)
      (sliceOverProjection (SSet.yonedaEquiv.symm y)) (verdierDenominatorOverSource i x) := by
  have h := fullRestriction_isPullback _ _ (verdierDenominatorSpanSliceLeft i x y)
    (sliceOverCoproductLeft (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y))
      (verdierDenominatorSpanSliceLeft_ι i x y) (fun _ hv => hv)
  exact h.paste_horiz (isPullback_sliceOverCoproduct
    (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y))

/-- 実分母・次辺の全空間は、二終点上の同じ実 marked slice と厳密に同型。 -/
def verdierDenominatorSpanSliceIso {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) : (verdierDenominatorSpanSlice i x y : SSet.{u}) ≅
      verdierDenominatorSpanFamily i x y :=
  (isPullback_verdierDenominatorSpanSlice i x y).isoPullback

lemma verdierDenominatorSpanSliceIso_denominator {A B : StableCategory.{u}}
    (i : ExactMap A B) (x y : B.obj _⦋0⦌) :
    (verdierDenominatorSpanSliceIso i x y).hom ≫ verdierDenominatorSpanProjection i x y =
      verdierDenominatorSpanSliceLeft i x y :=
  (isPullback_verdierDenominatorSpanSlice i x y).isoPullback_hom_snd

lemma verdierDenominatorSpanSliceIso_numerator {A B : StableCategory.{u}}
    (i : ExactMap A B) (x y : B.obj _⦋0⦌) :
    (verdierDenominatorSpanSliceIso i x y).hom ≫ verdierDenominatorSpanNumerator i x y =
      verdierDenominatorSpanSliceRight i x y :=
  (isPullback_verdierDenominatorSpanSlice i x y).isoPullback_hom_fst

end SerrePositivity.KST.LocalizingInvariants
