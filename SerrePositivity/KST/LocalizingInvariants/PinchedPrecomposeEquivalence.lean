module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.PointwiseUnitComparison

/-!
概要：可逆な h C の射による右写像空間の前合成は実際の同値。
方針：元の逆射を逆関手とし、前合成の合成則と単位則で両合成を比較する。
規約：始域の対象を等号で置き換えない。使われ方：K-8 の指定単位による随伴判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.PinchedPrecompose

variable {X : SSet.{u}} [Quasicategory X] {x x' : X _⦋0⦌}

def equivalence (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x x') (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x' y) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose y e.hom
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose y e.inv
  homInvIso := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precomposeCompIso y e.inv e.hom
    rw [Iso.inv_hom_id] at h
    exact h ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precomposeIdIso x' y
  invHomIso := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precomposeCompIso y e.hom e.inv
    rw [Iso.hom_inv_id] at h
    exact h ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precomposeIdIso x y

lemma isQCatEquivalence (f : (SSet.HomotopyCategory.mk x : hoFunctor.obj X) ⟶
    SSet.HomotopyCategory.mk x') [IsIso f] (y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.precompose y f) :=
  (equivalence (asIso f) y).isQCatEquivalence

end SerrePositivity.KST.LocalizingInvariants.PinchedPrecompose
