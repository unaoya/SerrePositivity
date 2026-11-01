module
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatModuleNerve
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 元の通常 tensor は、K-flat 入力の各実頂点を K-flat 出力へ送る。 -/
lemma dgRelativeKFlatKernel_vertex (P : Bimodule R E D)
    (hP : Bimodule.rightRelativeKFlat R E D P)
    (x : (dgRelativeKFlatModuleNerve R D) _⦋0⦌) :
    dgModuleRelativeKFlatVertex R E
      ((dgRelativeKFlatModuleInclusion R D ≫ dgNerve.map (Morita.kernelTensor R D E P)).app
        (Opposite.op ⦋0⦌) x) := by
  change moduleRelativeKFlat R E
    ((Morita.kernelTensor R D E P).obj (Simplex.vertexEquiv x.val))
  exact Morita.kernelTensor_relativeKFlat R D E P hP _
    (fullSubcomplexOnVertices_vertex x)
/-- 右相対 K-flat kernel の元の通常 tensor による、K-flat 全部分 ∞ 圏間の実写像。 -/
def dgRelativeKFlatKernelNerve (P : Bimodule R E D)
    (hP : Bimodule.rightRelativeKFlat R E D P) :
    dgRelativeKFlatModuleNerve R D ⟶ dgRelativeKFlatModuleNerve R E :=
  fullSubcomplexLift (dgModuleRelativeKFlatVertex R E)
    (dgRelativeKFlatModuleInclusion R D ≫ dgNerve.map (Morita.kernelTensor R D E P))
    (dgRelativeKFlatKernel_vertex R D E P hP)
/-- 構成した全単体写像の実包含像は、元の通常 dg tensor の nerve そのもの。 -/
lemma dgRelativeKFlatKernelNerve_inclusion (P : Bimodule R E D)
    (hP : Bimodule.rightRelativeKFlat R E D P) :
    dgRelativeKFlatKernelNerve R D E P hP ≫ dgRelativeKFlatModuleInclusion R E =
      dgRelativeKFlatModuleInclusion R D ≫ dgNerve.map (Morita.kernelTensor R D E P) :=
  fullSubcomplexLift_ι _ _ (dgRelativeKFlatKernel_vertex R D E P hP)
end SerrePositivity.InfinityCategories
