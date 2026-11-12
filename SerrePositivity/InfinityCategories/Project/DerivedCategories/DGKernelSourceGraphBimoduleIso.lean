module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelSourceGraphComparison
public import SerrePositivity.DifferentialGraded.Tensor.Compose
public import SerrePositivity.DifferentialGraded.Tensor.Triple
/-!
概要：同じ graph 合成双加群を、元の kernel の始域制限へ全 Hom 自然に同定する。
方針：指定の通常 tensor と全 Hom 自然な実同型、同じ出力分解を使う。
規約：元の Hom の平坦性と出力の射影性を仮定しない。
使われ方：一般 kernel の入力模型移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 同じ graph 合成双加群は、元の kernel の始域制限と全 Hom 自然に同型。 -/
def dgKernelSourceGraphBimoduleIso (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C D) (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.compose R E D C P (_root_.SerrePositivity.DifferentialGraded.functorGraph R C D F)) ≅
      _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E C (F.comp P) := by
  have h : _root_.SerrePositivity.DifferentialGraded.functorGraph R C D F =
      _root_.SerrePositivity.DifferentialGraded.Bimodule.leftRestriction R D D C F (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D) := rfl
  rw [h]
  exact _root_.SerrePositivity.DifferentialGraded.BimoduleTensor.composeLeftRestrictionIso R E D D C F
      (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R E D P) (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.of R D D (_root_.SerrePositivity.DifferentialGraded.Bimodule.diagonal R D)) ≪≫
    (_root_.SerrePositivity.DifferentialGraded.BimoduleCategory.middleLeftRestrictionFunctor R E D C F).mapIso
      (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightBimoduleUnitIso R E D P)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
