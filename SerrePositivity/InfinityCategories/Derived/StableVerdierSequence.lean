module
public import SerrePositivity.InfinityCategories.Derived.ExactFunctorCategoryEquivalence
public import SerrePositivity.InfinityCategories.Stable.Definition
/-!
概要：安定 ∞ 圏の Verdier 列を全完全関手 ∞ 圏の普遍性で定義する。
方針：完全充満忠実な包含と完全な零化射に、全自然変換を含む商普遍性を課す。
規約：冪等完備化を追加しない。使われ方：Drinfeld 商の Verdier 列。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
/-- 安定 ∞ 圏の包含と商が作る、全完全関手 ∞ 圏の意味での Verdier 列。 -/
structure IsStableVerdierSequence {B X Q : SSet.{u}}
    [Quasicategory B] [IsStable B] [Quasicategory X] [IsStable X]
    [Quasicategory Q] [IsStable Q] (i : B ⟶ X) (q : X ⟶ Q) : Prop where
  fullyFaithful : IsFullyFaithful i
  inclusionExact : IsExactFunctor i
  quotientExact : IsExactFunctor q
  kills (z : B _⦋0⦌) : IsZeroVertex ((i ≫ q).app (Opposite.op ⦋0⦌) z)
  universal (Y : SSet.{u}) [Quasicategory Y] [IsStable Y] :
    let := quotientExact
    IsQCatEquivalence (zeroingExactPrecomposition q (Set.range (i.app (Opposite.op ⦋0⦌)))
      (by rintro _ ⟨z, rfl⟩; exact kills z) Y)
end SerrePositivity.InfinityCategories
