module
public import SerrePositivity.InfinityCategories.Derived.DGKernelCellModelComparison
public import SerrePositivity.InfinityCategories.Core.FunctorIsoWhiskerComposition
/-!
概要：任意の二 kernel の指定平坦模型を通常 tensor で合成し、右相対 K-flat 性を保つ。
方針：同じ指定模型、実加群圏の比較同型と右相対 K-flat 時の実導来合成を使う。
規約：元の kernel と Hom の平坦性・出力の射影性を仮定しない。
使われ方：一般 kernel の合成と全 coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E K : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R K] [Small.{u} K]
/-- 任意の二 kernel の指定した両端平坦模型の通常合成双加群。 -/
def dgKernelCellComposite (P : Bimodule R E D) (Q : Bimodule R K E) :
    Bimodule R (DGCategoryCellResolution.Source R K) (DGCategoryCellResolution.Source R D) :=
  BimoduleTensor.compose R (DGCategoryCellResolution.Source R K)
    (DGCategoryCellResolution.Source R E) (DGCategoryCellResolution.Source R D)
    (BimoduleCategory.underlying R _ _ (dgKernelCellModel R E K Q))
    (BimoduleCategory.underlying R _ _ (dgKernelCellModel R D E P))
/-- 指定平坦模型の通常合成も右相対 K-flat。 -/
lemma dgKernelCellComposite_rightRelativeKFlat (P : Bimodule R E D) (Q : Bimodule R K E) :
    Bimodule.rightRelativeKFlat R (DGCategoryCellResolution.Source R K)
      (DGCategoryCellResolution.Source R D) (dgKernelCellComposite R D E K P Q) := by
  intro d
  exact Morita.kernelTensor_relativeKFlat R (DGCategoryCellResolution.Source R E)
    (DGCategoryCellResolution.Source R K)
    (BimoduleCategory.underlying R _ _ (dgKernelCellModel R E K Q))
    (dgKernelCellModel_rightRelativeKFlat R E K Q)
    (ForgetEnrichment.of (Complex R)
      ((BimoduleCategory.underlying R _ _ (dgKernelCellModel R D E P)).rightAt d))
    (dgKernelCellModel_rightRelativeKFlat R D E P d)
end SerrePositivity.InfinityCategories
