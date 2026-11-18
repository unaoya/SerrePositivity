module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakAnodyneLocalization

/-!
# 同じ弱な屋根族による実比較関手の充満忠実性の検出

DAG XIII §2.2 の native な忘却の降下の補助。両写像空間の抽象的な同値の存在に
置き換えず、指定関手の誘導射との同じ合成の弱同値性を検査する。［一般∞］移動候補。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open FullFaithfulAndEssentiallySurjectiveFunctors MorphismSpaces.Basic
open scoped Simplicial

/-- 元の各写像空間に入る同じ弱な族とその像で、実関手の充満忠実性を検出する。 -/
lemma fullyFaithful_of_weak_roof {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (F : C ⟶ D)
    (h : ∀ x y : C _⦋0⦌, ∃ (K : SSet.{u}) (p : K ⟶ pinchedHom x y),
      IsWeakHomotopyEquivalence p ∧
        IsWeakHomotopyEquivalence (p ≫ pinchedHomMap F x y)) : IsFullyFaithful F := by
  intro x y
  obtain ⟨K, p, hp, hc⟩ := h x y
  exact (hp.cancel_left hc).isSimplicialHomotopyEquivalence

end SerrePositivity.EInfinity.PowerOperation
