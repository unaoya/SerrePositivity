module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelCellSourceComparison
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.KFlatness
public import SerrePositivity.DifferentialGraded.Bimodule.Value
/-!
概要：任意の元の kernel を両端の cell 分解へ制限し、同じ半自由双加群分解を指定する。
方針：両作用の実制限と、平坦な cell 始域上の実半自由分解を使う。
規約：元の dg 圏には局所 Hom 平坦性を仮定しない。
使われ方：一般 kernel の実導来作用と合成を平坦模型上で計算する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 元の kernel の両端の cell 増大に沿う、同じ実双加群の制限。 -/
def dgKernelCellRestriction (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
      (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) :=
  (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleRightRestrictionFunctor R E (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R E)).obj
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D)
        ((_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.augmentation R D).comp P))
/-- 両端を cell 分解へ制限した kernel の指定半自由双加群分解。 -/
def dgKernelCellResolution (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    _root_.SerrePositivity.DifferentialGraded.BimoduleSemifreeResolution R (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
      (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) (dgKernelCellRestriction R D E P) :=
  _root_.SerrePositivity.DifferentialGraded.bimoduleCanonicalSemifreeResolution R (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) (dgKernelCellRestriction R D E P)
/-- 両端の cell 分解上の指定 kernel 模型。 -/
def dgKernelCellModel (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
      (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D) :=
  (dgKernelCellResolution R D E P).obj
/-- 指定模型は、元の Hom の平坦性を仮定せず右相対 K-flat。 -/
lemma dgKernelCellModel_rightRelativeKFlat (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R E)
      (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.Source R D)
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.underlying R _ _ (dgKernelCellModel R D E P)) :=
  (dgKernelCellResolution R D E P).rightRelativeKFlat R _ _
    (_root_.SerrePositivity.DifferentialGraded.DGCategoryCellResolution.source_homKFlat R D)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
