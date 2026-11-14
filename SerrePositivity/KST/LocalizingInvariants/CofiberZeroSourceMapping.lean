module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.LocalizingInvariants.ReflectiveIsoTargetMapping
public import SerrePositivity.KST.LocalizingInvariants.CofiberZeroSourceComparison

/-!
概要：零始点矢印を終点とする元の cofiber 関手の写像空間比較は同値。
方針：同じ終点の右随伴像との実同型を使い、反射の写像空間比較を移す。
規約：元の cofiber 選択による pinchedHomMap。使われ方：元の差の関手への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]

/-- 零始点の元の矢印は、その実終点を右随伴へ入れた矢印と同型。 -/
def cofiberZeroSourceVertexIso (z : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌)
    (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso z ((cofiberRightAdjoint X).app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.target X).app (Opposite.op ⦋0⦌) z)) := by
  let a : (Δ[0] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X := SSet.const z
  have ha : ∀ w, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow (a.app (Opposite.op ⦋0⦌) w) := by
    intro w
    dsimp only [a]
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex]
    exact hz
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.app (zeroSourceArrowComparison X a ha)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((SSet.const z : (Δ[0] : SSet.{u}) ⟶ _).app (Opposite.op ⦋0⦌) _)
    ((cofiberRightAdjoint X).app (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.target X).app
      (Opposite.op ⦋0⦌) ((SSet.const z : (Δ[0] : SSet.{u}) ⟶ _).app
        (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 1))))) at e
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagram_const_vertex] at e
  exact e

lemma cofiberZeroSourceMapping_equivalence
    (x z : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroSourceArrow z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber X (𝟙 ((ihom (Δ[1] : SSet.{u})).obj X))) x z) :=
  reflectiveIsoTargetPinchedHomMap_equivalence (cofiberAdjunction X)
    (cofiberRightAdjoint_fullyFaithful X) x z ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.target X).app (Opposite.op ⦋0⦌) z)
    (cofiberZeroSourceVertexIso X z hz)

end SerrePositivity.KST.LocalizingInvariants

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Tamme "Eq (8)"] _root_.SerrePositivity.KST.LocalizingInvariants.cofiberZeroSourceMapping_equivalence
attribute [cite Tamme "Eq (8)"] _root_.SerrePositivity.KST.LocalizingInvariants.cofiberZeroSourceVertexIso
