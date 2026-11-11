module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullDiagonalComparison

/-!
概要：元実／絶対共有対角の同じ完全関手が零合成の終成分に属すことを回収する。
方針：同じ元零 Hom 頂点と元 Hom 包含の厳密回収を使う。
規約：元の対角射を選び直さない。使われ方：実比較 prism の全 Hom の零性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)

/-- 概要：元実共有対角完全射は同じ元完全関手圏の終対象。
方針：元実対角の零 Hom 頂点の包含を厳密回収する。
規約：元の実射を保持。使われ方：実比較二胞体の全 Hom の終成分判定。 -/
lemma dgOdotMilnorNuNullDiagonalMap_isTerminal (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv (K) (B) (dgOdotMilnorNuNullDiagonalMap R d)) := by
  have he : (dgOdotMilnorNuNullDiagonalVertex R d).val =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv (K) (B) (dgOdotMilnorNuNullDiagonalMap R d) :=
    congrArg Subtype.val (dgOdotMilnorNuNullDiagonalComparison_source R d h)
  exact he ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (dgOdotMilnorNuNullDiagonalVertex R d)

/-- 概要：元絶対共有対角完全射は同じ元完全関手圏の終対象。
方針：元絶対対角の零 Hom 頂点の包含を厳密回収する。
規約：同じ元絶対射を保持。使われ方：実比較二胞体の全 Hom の終成分判定。 -/
lemma dgOdotMilnorNuAbsoluteDiagonalMap_isTerminal :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv (K) (B)
      (dgOdotMilnorNuAbsoluteDiagonalMap R d h)) := by
  have he : (dgOdotMilnorNuAbsoluteDiagonalVertex R d h).val =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv (K) (B) (dgOdotMilnorNuAbsoluteDiagonalMap R d h) :=
    congrArg Subtype.val (dgOdotMilnorNuNullDiagonalComparison_target R d h)
  exact he ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (dgOdotMilnorNuAbsoluteDiagonalVertex R d h)

end SerrePositivity.KST.SConstruction
