module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctionPinchedSpaces
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceModelEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal

/-!
概要：指定した随伴の左関手は始頂点を、右関手は終頂点を保つ。
方針：同じ随伴の写像空間比較に可縮性を移し、始終対象の境界判定へ戻す。
使われ方：HTT 5.2.3.5、Kerodon §6.2（Tag 02EH）の随伴の保存則。
規約：ホモトピー圏の始終対象だけへ弱めず、元の準圏の頂点について示す。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction

/-- 同じ随伴の左関手は、元の始頂点を保つ。 -/
lemma left_preservesInitialVertex {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G)
    (x : X _⦋0⦌) (hx : IsInitialVertex x) : IsInitialVertex (F.app _ x) := by
  apply isInitialVertex_of_pinchedHomLeft_isContractibleKan
  intro y
  exact (pinchedHomLeftRightEquivalence _ y).isContractibleKan_iff.mpr
    ((a.pinchedHomEquivalence x y).isContractibleKan_iff.mpr
      ((pinchedHomLeftRightEquivalence x _).isContractibleKan_iff.mp
        (hx.pinchedHomLeft_isContractibleKan _)))

/-- 同じ随伴の右関手は、元の終頂点を保つ。 -/
lemma right_preservesTerminalVertex {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G)
    (y : Y _⦋0⦌) (hy : IsTerminalVertex y) : IsTerminalVertex (G.app _ y) := by
  apply isTerminalVertex_of_pinchedHom_isContractibleKan
  intro x
  exact (a.pinchedHomEquivalence x y).isContractibleKan_iff.mp
    (hy.pinchedHom_isContractibleKan _)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction
