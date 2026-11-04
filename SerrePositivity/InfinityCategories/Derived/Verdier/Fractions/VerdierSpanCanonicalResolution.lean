module

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierSpanBoundarySlice
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFractionComparisonResolution
public import SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionMaps

/-!
概要：実分母・次辺族と元の実 span 族の比較経路を保持した置換。
方針：実 slice 比較の全同値を使い、両射影の全境界充填を証明する。
規約：標的は未完成の実 span。完成分数から実族への充填は別の工程。
使われ方：指定部分族を保持した実分母・次辺族の回収と、亜群化比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}

/-- 実分母・次辺族と元の実 span の全比較経路を記憶する。 -/
def verdierSpanCanonicalResolution (i : ExactMap A B) (x y : B.obj _⦋0⦌) : SSet.{u} :=
  equivalencePathReplacement (verdierDenominatorSpanCanonicalComparison i x y)

def verdierSpanCanonicalResolutionRoof (i : ExactMap A B) (x y : B.obj _⦋0⦌) :
    verdierSpanCanonicalResolution i x y ⟶ verdierDenominatorSpanFamily i x y :=
  equivalencePathReplacementProjection _

def verdierSpanCanonicalResolutionMap (i : ExactMap A B) (x y : B.obj _⦋0⦌) :
    verdierSpanCanonicalResolution i x y ⟶
      fixedMarkedSpans B.obj (weakEquivalences i) x y :=
  equivalencePathReplacementMap _

instance verdierSpanCanonicalResolutionRoof_trivialKanFibration
    (i : ExactMap A B) (x y : B.obj _⦋0⦌) :
    TrivialKanFibration (verdierSpanCanonicalResolutionRoof i x y) :=
  equivalencePathReplacementProjection_trivialKanFibration _

lemma verdierSpanCanonicalResolutionMap_trivialKanFibration
    (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌) :
    TrivialKanFibration (verdierSpanCanonicalResolutionMap i x y) := by
  have he := verdierDenominatorSpanCanonicalComparison_isQCatEquivalence h x y
  exact he.choose.isFullyFaithful.equivalencePathReplacementMap.trivialKanFibration_of_surjective
    he.choose.isEssentiallySurjective.equivalencePathReplacementMap_surjective

/-- 同じ実分母・次辺族と実 span 族を結ぶ全関手同型。 -/
def verdierSpanCanonicalResolutionIso (i : ExactMap A B) (x y : B.obj _⦋0⦌) :
    FunctorIso (verdierSpanCanonicalResolutionRoof i x y ≫
      verdierDenominatorSpanCanonicalComparison i x y)
      (verdierSpanCanonicalResolutionMap i x y) :=
  equivalencePathReplacementFunctorIso _

/-- 指定部分族を保ち、元の実 span 全族を実分母・次辺族へ回収する。 -/
lemma exists_relative_verdierSpanCanonicalFamily (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {S T : SSet.{u}} (j : S ⟶ T) [Mono j]
    (a : S ⟶ verdierSpanCanonicalResolution i x y)
    (b : T ⟶ fixedMarkedSpans B.obj (weakEquivalences i) x y)
    (ha : a ≫ verdierSpanCanonicalResolutionMap i x y = j ≫ b) :
    ∃ F : T ⟶ verdierSpanCanonicalResolution i x y,
      j ≫ F = a ∧ F ≫ verdierSpanCanonicalResolutionMap i x y = b := by
  let := verdierSpanCanonicalResolutionMap_trivialKanFibration h x y
  have := TrivialKanFibration.mem (p := verdierSpanCanonicalResolutionMap i x y)
    j inferInstance
  have sq : CommSq a j (verdierSpanCanonicalResolutionMap i x y) b := ⟨ha⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- 実族の標準比較を亜群化しても、元の全関手同値を保つ。 -/
lemma verdierSpanCanonicalCompletionMap_isQCatEquivalence
    (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌) :
    IsQCatEquivalence
      (groupoidCompletionMapOf (verdierDenominatorSpanCanonicalComparison i x y)) :=
  groupoidCompletionMapOf_isQCatEquivalence
    (verdierDenominatorSpanCanonicalComparison_isQCatEquivalence h x y)

/-- 実族の亜群化を、同じ商の写像空間へ元の完成分数比較で評価する。 -/
def verdierSpanCanonicalCompletionComparison (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) : groupoidCompletion (verdierDenominatorSpanFamily i x y) ⟶
      intervalMappingSpace (q.hom.app (Opposite.op ⦋0⦌) x)
        (q.hom.app (Opposite.op ⦋0⦌) y) :=
  groupoidCompletionMapOf (verdierDenominatorSpanCanonicalComparison i x y) ≫
    fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y

lemma verdierSpanCanonicalCompletionComparison_isQCatEquivalence
    (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌) :
    IsQCatEquivalence (verdierSpanCanonicalCompletionComparison h x y) :=
  (verdierSpanCanonicalCompletionMap_isQCatEquivalence h x y).comp
    (weakFractionMappingComparison_isQCatEquivalence h x y)

end SerrePositivity.KST.LocalizingInvariants
