module
public import SerrePositivity.KST.SConstruction.DGKFixedInterface
public import SerrePositivity.InfinityCategories.F1.Coherent.EdgeEquiv
public import SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagrams

/-! # 固定 dg 入力の同じ一単体から、元の対象二つと厳密 dg 射を回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (A : Type u) [CommRing A]

/-- 元の一単体の、端点を含む同じ通常 dg 入力射のデータ。 -/
def dgInputArrowData (s : (dgKInputInfinity.{u, v} A) _⦋1⦌) :
    Σ P Q : PerfDGInput.{u, v} A, P ⟶ Q := coherentNerveArrowData s

/-- 復元した通常の射は、元の同じ一単体を厳密に回収する。 -/
theorem dgInputArrowData_edge (s : (dgKInputInfinity.{u, v} A) _⦋1⦌) :
    (coherentNerveEdge (dgInputArrowData A s).2.2).edge = s :=
  (coherentNerveArrowDataEquiv (PerfDGInput.{u, v} A)).symm_apply_apply s

/-- 回収した同じ通常 dg 射の ν 辺は、元の一単体の ν 像と等しい。 -/
theorem dgInputArrowData_nu_edge (s : (dgKInputInfinity.{u, v} A) _⦋1⦌) :
    (coherentNerveEdge (dgKInputNuMap A (dgInputArrowData A s).2.2)).edge =
      (dgKInputNu A).app (Opposite.op ⦋1⦌) s :=
  (dgKInputNu_edge A (dgInputArrowData A s).2.2).symm.trans
    (congrArg ((dgKInputNu A).app (Opposite.op ⦋1⦌)) (dgInputArrowData_edge A s))

private theorem essentialSurjectivity_of_same_edge
    {B C D E : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
    (he : (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow q).edge = (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow r).edge)
    (hr : IsEssentiallySurjective r.hom) : IsEssentiallySurjective q.hom := by
  have h := congrArg (fun e : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} _⦋1⦌ =>
    IsEssentiallySurjective (coherentNerveArrowData (C := _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableQCat.{u}) e).2.2.hom) he
  simp only [_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow, coherentNerveEdge_edge] at h
  exact h.mpr hr

/-- 同じ ν 辺が本質的全射な完全関手の辺なら、復元した同じ dg 射の ν 作用も本質的全射。 -/
theorem dgInputArrowData_nu_essentiallySurjective
    (s : (dgKInputInfinity.{u, v} A) _⦋1⦌)
    {B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{max (u + 1) v}} (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C)
    (he : (dgKInputNu A).app (Opposite.op ⦋1⦌) s = (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow q).edge)
    (hq : IsEssentiallySurjective q.hom) :
    IsEssentiallySurjective (dgKInputNuMap A (dgInputArrowData A s).2.2).hom :=
  essentialSurjectivity_of_same_edge _ q ((dgInputArrowData_nu_edge A s).trans he) hq

end SerrePositivity.KST.Fibration
