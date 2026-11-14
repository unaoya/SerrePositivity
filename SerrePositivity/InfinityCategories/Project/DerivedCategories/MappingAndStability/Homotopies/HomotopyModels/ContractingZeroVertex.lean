module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.ContractingInitialVertex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.ContractingTerminalVertex
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.Pointed

/-! # 収縮元を持つ dg 対象の零対象性

概要：次数 −1 の収縮元を持つ対象は dg nerve の零対象。
方針：実境界充填による始対象性と写像空間による終対象性を合わせる。
規約：通常の h の零性だけを使わない。使われ方：β3 の商による零化。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 収縮元を持つ対象は dg nerve の零頂点。 -/
lemma dgNerve_contractingElement_isZeroVertex (x : D) (h : _root_.SerrePositivity.DifferentialGraded.GradedHom A x x (-1))
    (dh : (_root_.SerrePositivity.DifferentialGraded.homObject A D x x).d (-1) 0 h = (_root_.SerrePositivity.DifferentialGraded.unitElement A x).val) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_contractingElement_isInitialVertex x h dh,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.dgNerve_contractingElement_isTerminalVertex x h dh⟩

/-- 収縮元付き対象を選ばれた零頂点としてまとめる。 -/
def dgNerveContractingZeroVertex (x : D) (h : _root_.SerrePositivity.DifferentialGraded.GradedHom A x x (-1))
    (dh : (_root_.SerrePositivity.DifferentialGraded.homObject A D x x).d (-1) 0 h = (_root_.SerrePositivity.DifferentialGraded.unitElement A x).val) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_contractingElement_isInitialVertex x h dh,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.dgNerve_contractingElement_isTerminalVertex x h dh⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
