module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

/-- 元の順序を保持した二終点の固定図式。 -/
def spanTwoPointDiagram {X : SSet.{u}} (x y : X _⦋0⦌) :
    (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X :=
  coprod.desc (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y)

/-- 二終点上の実 slice の、左脚が元の分母である全部分複体。 -/
def verdierDenominatorSpanSlice {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B)
    (x y : B.obj _⦋0⦌) : (sliceOver (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanTwoPointDiagram x y)).Subcomplex :=
  fullSubcomplexOnVertices _ (fun v =>
    (roofPointSliceVertexEdge (SSet.yonedaEquiv.symm x)
      ((sliceOverCoproductLeft (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y)).app
        (Opposite.op ⦋0⦌) v)).edge ∈ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i)

instance verdierDenominatorSpanSlice_quasicategory {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) (x y : B.obj _⦋0⦌) :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSlice i x y : SSet.{u}) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSlice]
  infer_instance

/-- 同じ単一の実錐から、元の実分母を回収する。 -/
def verdierDenominatorSpanSliceLeft {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B)
    (x y : B.obj _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSlice i x y : SSet.{u}) ⟶
      (verdierDenominatorOver i x : SSet.{u}) :=
  fullSubcomplexLift _ ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSlice i x y).ι ≫
    sliceOverCoproductLeft (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y))
      (fun v => fullSubcomplexOnVertices_vertex v)

/-- 同じ単一の実錐から、元の実次辺を回収する。 -/
def verdierDenominatorSpanSliceRight {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B)
    (x y : B.obj _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSlice i x y : SSet.{u}) ⟶
      sliceOver (SSet.yonedaEquiv.symm y) :=
  (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSlice i x y).ι ≫
    sliceOverCoproductRight (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y)

lemma verdierDenominatorSpanSliceLeft_ι {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B)
    (x y : B.obj _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceLeft i x y ≫
      (verdierDenominatorOver i x).ι = (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSlice i x y).ι ≫
        sliceOverCoproductLeft (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y) :=
  fullSubcomplexLift_ι _ _ _

/-- 分母条件へ制限しても、元の二つの実始域上の引き戻しを保持する。 -/
lemma isPullback_verdierDenominatorSpanSlice {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B)
    (x y : B.obj _⦋0⦌) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceRight i x y) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceLeft i x y)
      (sliceOverProjection (SSet.yonedaEquiv.symm y)) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorOverSource i x) := by
  have h := fullRestriction_isPullback _ _ (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceLeft i x y)
    (sliceOverCoproductLeft (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y))
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceLeft_ι i x y) (fun _ hv => hv)
  exact h.paste_horiz (isPullback_sliceOverCoproduct
    (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y))

/-- 実分母・次辺の全空間は、二終点上の同じ実 marked slice と厳密に同型。 -/
def verdierDenominatorSpanSliceIso {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B)
    (x y : B.obj _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSlice i x y : SSet.{u}) ≅
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x y :=
  (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.isPullback_verdierDenominatorSpanSlice i x y).isoPullback

lemma verdierDenominatorSpanSliceIso_denominator {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) (x y : B.obj _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceIso i x y).hom ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceLeft i x y :=
  (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.isPullback_verdierDenominatorSpanSlice i x y).isoPullback_hom_snd

lemma verdierDenominatorSpanSliceIso_numerator {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) (x y : B.obj _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceIso i x y).hom ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanNumerator i x y =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceRight i x y :=
  (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.isPullback_verdierDenominatorSpanSlice i x y).isoPullback_hom_fst

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.isPullback_verdierDenominatorSpanSlice := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.isPullback_verdierDenominatorSpanSlice

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanTwoPointDiagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanTwoPointDiagram := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanTwoPointDiagram

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSlice (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanSlice := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSlice

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanSliceIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanSliceIso_denominator := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceIso_denominator

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanSliceIso_numerator := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceIso_numerator

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceLeft (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanSliceLeft := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceLeft

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanSliceLeft_ι := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceLeft_ι

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceRight (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanSliceRight := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceRight

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSlice_quasicategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanSlice_quasicategory := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSlice_quasicategory

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanTwoPointDiagram._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanTwoPointDiagram._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanSliceIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanSliceLeft._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanSliceLeft._proof_1
