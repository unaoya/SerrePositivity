module

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierDenominatorSpanFamily
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFractionComparisonResolution
public import SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionMaps
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RightIntervalEquivalence

/-!
概要：実分母上の次辺族を、元の完成分数比較と全比較経路で結ぶ。
方針：固定端点 span への実貼合せと、同じ亜群化単位の全関手同型を使う。
規約：実族から完成族への比較の同値性は、この接続だけでは主張しない。
使われ方：実分母添字での有限因子化と完成分数の全写像空間比較との接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

/-- 指定実分母上の全次辺 fiber を、元の右 pinched Hom と厳密に同定する。 -/
def verdierDenominatorSpanPinchedFiberIso {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌) :
    vertexFiber (verdierDenominatorSpanProjection i x y) d ≅
      pinchedHom ((verdierDenominatorOverSource i x).app (Opposite.op ⦋0⦌) d) y :=
  verdierDenominatorSpanFiberIso i x y d ≪≫ (pinchedHomSliceFiberIso _ _).symm

/-- 同じ実次辺 fiber から、同じ実始域・終点の区間写像空間への比較。 -/
def verdierDenominatorSpanFiberComparison {A B : StableCategory.{u}} (i : ExactMap A B)
    (x y : B.obj _⦋0⦌) (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌) :
    vertexFiber (verdierDenominatorSpanProjection i x y) d ⟶
      intervalMappingSpace ((verdierDenominatorOverSource i x).app (Opposite.op ⦋0⦌) d) y :=
  (verdierDenominatorSpanPinchedFiberIso i x y d).hom ≫ pinchedHomToIntervalMappingSpace _ _

/-- 各実分母上の比較は、元の全 Kan 写像空間の同値。 -/
lemma verdierDenominatorSpanFiberComparison_isQCatEquivalence
    {A B : StableCategory.{u}} (i : ExactMap A B) (x y : B.obj _⦋0⦌)
    (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌) :
    IsQCatEquivalence (verdierDenominatorSpanFiberComparison i x y d) :=
  (qCatEquivalenceOfIso (verdierDenominatorSpanPinchedFiberIso i x y d)).isQCatEquivalence.comp
    (pinchedHomToIntervalMappingSpace_isQCatEquivalence _ _)

/-- 同じ元の分数評価を、実分母・次辺の全空間へ制限する。 -/
def verdierDenominatorSpanEvaluation {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) : verdierDenominatorSpanFamily i x y ⟶
      intervalMappingSpace (q.hom.app (Opposite.op ⦋0⦌) x)
        (q.hom.app (Opposite.op ⦋0⦌) y) :=
  verdierDenominatorSpanToFixed i x y ≫ fixedFractionEvaluation q.hom
    (weakEquivalences i) h.inverts x y

/-- 実族を元の固定端点分数と同じ完成分数へ送る射。 -/
def verdierDenominatorSpanCompletionMap {A B : StableCategory.{u}}
    (i : ExactMap A B) (x y : B.obj _⦋0⦌) :
    groupoidCompletion (verdierDenominatorSpanFamily i x y) ⟶
      groupoidCompletion (fixedMarkedSpans B.obj (weakEquivalences i) x y) :=
  groupoidCompletionMapOf (verdierDenominatorSpanToFixed i x y)

/-- 亜群化後も Sp-6 s4 の元の分数比較をそのまま使う。 -/
def verdierDenominatorSpanCompletionComparison {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) : groupoidCompletion (verdierDenominatorSpanFamily i x y) ⟶
      intervalMappingSpace (q.hom.app (Opposite.op ⦋0⦌) x)
        (q.hom.app (Opposite.op ⦋0⦌) y) :=
  verdierDenominatorSpanCompletionMap i x y ≫
    fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y

/-- 元の実分母・次辺の全族と商族を、同じ全比較経路で結ぶ。 -/
def verdierDenominatorSpanCompletionComparison_unitIso {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) :
    FunctorIso (groupoidCompletionMap (verdierDenominatorSpanFamily i x y) ≫
      verdierDenominatorSpanCompletionComparison h x y)
      (verdierDenominatorSpanEvaluation h x y) := by
  have e := FunctorIso.postcomp (groupoidCompletionMapOfIso (verdierDenominatorSpanToFixed i x y))
    (fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y)
  have f := FunctorIso.precomp
    (fractionMappingComparisonIso q.hom (weakEquivalences i) h.inverts x y)
    (verdierDenominatorSpanToFixed i x y)
  simpa only [verdierDenominatorSpanCompletionComparison, verdierDenominatorSpanCompletionMap,
    verdierDenominatorSpanEvaluation, Category.assoc] using e ≪≫ f

end SerrePositivity.KST.LocalizingInvariants
