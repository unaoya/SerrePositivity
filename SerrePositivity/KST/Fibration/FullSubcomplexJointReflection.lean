module
public import SerrePositivity.KST.Fibration.JointReflection
public import SerrePositivity.KST.SConstruction.FullSubcomplexGappedReflection

/-! # 実普遍性の共同反映を元の充満部分図式圏へ制限する -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 両標的の包含が実普遍性を保つ場合、周囲での共同反映を元の充満部分圏へ移す。 -/
lemma JointlyReflectsSData.fullSubcomplex {P X A : SSet.{u}} [Quasicategory P]
    {p : P ⟶ X} {q : P ⟶ A} (h : JointlyReflectsSData p q)
    (RP : P _⦋0⦌ → Prop) (RX : X _⦋0⦌ → Prop) (RA : A _⦋0⦌ → Prop)
    {p' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices P RP : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X RX}
    {q' : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices P RP : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices A RA}
    (hp : p' ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X RX).ι = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices P RP).ι ≫ p)
    (hq : q' ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices A RA).ι = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices P RP).ι ≫ q)
    (hx : PreservesSConstructionData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X RX).ι)
    (ha : PreservesSConstructionData (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices A RA).ι) :
    JointlyReflectsSData p' q' where
  zero v hvp hvq := by
    have hvp' := hx.1 _ hvp
    have hvq' := ha.1 _ hvq
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((p' ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X RX).ι).app _ v) at hvp'
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((q' ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices A RA).ι).app _ v) at hvq'
    rw [hp] at hvp'
    rw [hq] at hvq'
    have hz := h.zero v.val hvp' hvq'
    exact ⟨isInitialVertex_fullSubcomplex_of_ambient RP v hz.1,
      isTerminalVertex_fullSubcomplex_of_ambient RP v hz.2⟩
  pushout F hFp hFq := by
    have hFp' := hx.2 _ hFp
    have hFq' := ha.2 _ hFq
    rw [Category.assoc, hp, ← Category.assoc] at hFp'
    rw [Category.assoc, hq, ← Category.assoc] at hFq'
    exact isPushoutSquare_fullSubcomplex_of_ambient RP F (h.pushout _ hFp' hFq')

end SerrePositivity.KST.Fibration
