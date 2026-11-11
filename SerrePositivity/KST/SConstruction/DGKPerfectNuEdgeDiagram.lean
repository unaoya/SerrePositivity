module
public import SerrePositivity.KST.SConstruction.DGKPerfectNuEquivalence

/-!
概要：固定 S の元辺の Cat^perf 像を全区間図式として回収する。
方針：元全一単体の回収と Yoneda の自然性を使う。
規約：元入力辺・固定 ν を保持。使われ方：実外周の四辺の指定表示。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial

/-- 概要：元入力辺の同じ Cat^perf 像は元完全射の全区間図式。
方針：同じ元一単体の ν 回収式を Yoneda で読む。
規約：全単体の厳密等号。使われ方：元実四角形の四境界表示。 -/
lemma dgKInputPerfectNu_edge_diagram (R : Type u) [CommRing R]
    {A B : PerfDGInput.{u, v} R} (f : A ⟶ B) :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow (dgKInputNuMap R f)
        (dgKInputStableValue_isIdempotentComplete R A)
        (dgKInputStableValue_isIdempotentComplete R B)).edge := by
  apply SSet.yonedaEquiv.injective
  let e : (dgKInputInfinity.{u, v} R) _⦋1⦌ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge
  let a : (Δ[1] : SSet) ⟶ dgKInputInfinity.{u, v} R := SSet.yonedaEquiv.symm e
  have h₁ := SSet.yonedaEquiv_comp a (dgKInputPerfectNu R)
  have h₂ := congrArg ((dgKInputPerfectNu R).app (Opposite.op ⦋1⦌))
    (Equiv.apply_symm_apply SSet.yonedaEquiv e)
  exact h₁.trans (h₂.trans ((dgKInputPerfectNu_edge R f).trans
    (Equiv.apply_symm_apply SSet.yonedaEquiv _).symm))
end SerrePositivity.KST.SConstruction
