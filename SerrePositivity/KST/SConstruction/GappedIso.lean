module
public import SerrePositivity.KST.SConstruction.ZeroPreservation
public import SerrePositivity.KST.SConstruction.ColimitDiagramTransport

/-! # gapped 条件の関手同型による不変性
概要：gapped 図式は coherent な関手同型で閉じ、関手圏の全零対象も gapped。
方針：各対角の零対象性と各正方形の普遍性を同型で移す。
規約：頂点ごとの単なる同型の族で代用しない。使われ方：cofiber 補完の零角。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：gapped 条件は関手全体の同型で保存される。
方針：対角の評価と正方形の制限で同型を写す。
規約：C は quasicategory。使われ方：普遍補完の選択の変更。 -/
lemma IsGapped.of_functorIso {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    {F G : arNerve n ⟶ C} (hF : IsGapped F) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) : IsGapped G := by
  constructor
  · intro i
    have ei := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ComposableArrows.mk₀ (arObj i i le_rfl)))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at ei
    exact (hF.1 i).of_vertexIso ei
  · intro i j k l hij hjk hkl
    exact IsPushoutSquare.of_functorIso (hF.2 i j k l hij hjk hkl)
      (e.precomp (arSquare i j k l hij hjk hkl))

/-- 概要：同型な二つの Ar 図式の gapped 条件は同値。
方針：同型と逆同型を使う。
規約：C は quasicategory。使われ方：完成した図式の gapped 性の比較。 -/
lemma isGapped_iff_of_functorIso {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    {F G : arNerve n ⟶ C} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) : IsGapped F ↔ IsGapped G :=
  ⟨fun h => IsGapped.of_functorIso h e, fun h => IsGapped.of_functorIso h e.symm⟩

/-- 概要：Ar 図式の関手圏の任意の零対象は gapped。
方針：定値零関手との同型を使って gapped 条件を移す。
規約：chosen zero への等号を仮定しない。使われ方：cofiber の零角の gapped 性。 -/
lemma isGapped_of_functorVertex_isZero {n : ℕ} {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C]
    (F : arNerve n ⟶ C) (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) : IsGapped F := by
  let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C
  let Z : arNerve n ⟶ C := SSet.const z.vertex
  have hZ := functor_const_isZeroVertex (A := arNerve n) z.vertex z.isZero
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso Z F := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.zeroVertexIso ⟨_, hZ.1, hZ.2⟩ ⟨_, hF.1, hF.2⟩
  exact IsGapped.of_functorIso (isGapped_const n z.vertex z.isZero) e

end SerrePositivity.KST.SConstruction
