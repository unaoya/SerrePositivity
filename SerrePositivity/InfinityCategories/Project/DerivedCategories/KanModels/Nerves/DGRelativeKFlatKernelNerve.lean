module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGRelativeKFlatModuleNerve
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKernel
/-!
概要：右相対 K-flat kernel の通常 tensor を、K-flat 頂点全部分 ∞ 圏上の実関手にする。
方針：元の dg tensor の nerve と実包含の合成を、K-flat 対象の保存条件で持ち上げる。
規約：入力や kernel の射影性は不要。使われ方：実導来合成子の coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 元の通常 tensor は、K-flat 入力の各実頂点を K-flat 出力へ送る。 -/
lemma dgRelativeKFlatKernel_vertex (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D)
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P)
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleNerve R D) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRelativeKFlatVertex R E
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P)).app
        (Opposite.op ⦋0⦌) x) := by
  change _root_.SerrePositivity.DifferentialGraded.moduleRelativeKFlat R E
    ((Morita.kernelTensor R D E P).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv x.val))
  exact _root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor_relativeKFlat R D E P hP _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex x)
/-- 右相対 K-flat kernel の元の通常 tensor による、K-flat 全部分 ∞ 圏間の実写像。 -/
def dgRelativeKFlatKernelNerve (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D)
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleNerve R D ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleNerve R E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleRelativeKFlatVertex R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P))
    (dgRelativeKFlatKernel_vertex R D E P hP)
/-- 構成した全単体写像の実包含像は、元の通常 dg tensor の nerve そのもの。 -/
lemma dgRelativeKFlatKernelNerve_inclusion (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D)
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P) :
    dgRelativeKFlatKernelNerve R D E P hP ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R E =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatModuleInclusion R D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Morita.kernelTensor R D E P) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ (dgRelativeKFlatKernel_vertex R D E P hP)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
