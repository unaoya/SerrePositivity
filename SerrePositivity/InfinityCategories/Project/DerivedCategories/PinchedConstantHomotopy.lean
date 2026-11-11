module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.ConstantEdgeFamily
/-!
概要：実 pinched 頂点の定数族のホモトピーを、元の実辺の全区間に同定する。
方針：区間表示の頂点公式と定数辺族の公式を使う。
規約：全時刻の写像を厳密に保つ。使われ方：実閉分母の像との底の照合。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
/-- 実 pinched 頂点の定数族は、元の実一次単体を全時刻の写像として持つ。 -/
lemma pinchedConstantHomotopy_h {K X : SSet.{u}} {x y : X _⦋0⦌}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy
      (SSet.const (X := K) s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y)).h =
        snd K (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm s.val := by
  rw [SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.intervalFamilyHomotopy_const_edge_h
    (SSet.Edge.ofTruncated (X := X) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv x y s))
/-- 後合成後の定数族も、同じ実一次単体の像を全時刻で持つ。 -/
lemma pinchedConstantHomotopy_postcomp_h {K X Y : SSet.{u}} (F : X ⟶ Y)
    {x y : X _⦋0⦌} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy
      ((SSet.const (X := K) s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F x y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)).h =
      snd K (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm (F.app (Opposite.op ⦋1⦌) s.val) := by
  rw [SSet.const_comp]
  exact pinchedConstantHomotopy_h ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F x y).app (Opposite.op ⦋0⦌) s)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
