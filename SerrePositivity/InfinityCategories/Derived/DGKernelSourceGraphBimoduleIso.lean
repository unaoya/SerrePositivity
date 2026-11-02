module
public import SerrePositivity.InfinityCategories.Derived.DGKernelSourceGraphComparison
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C D E : Type v)
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  [DGCategory R E] [Small.{u} E]
/-- 同じ graph 合成双加群は、元の kernel の始域制限と全 Hom 自然に同型。 -/
def dgKernelSourceGraphBimoduleIso (F : DGFunctor R C D) (P : Bimodule R E D) :
    BimoduleCategory.of R E C (BimoduleTensor.compose R E D C P (functorGraph R C D F)) ≅
      BimoduleCategory.of R E C (F.comp P) := by
  have h : functorGraph R C D F =
      Bimodule.leftRestriction R D D C F (Bimodule.diagonal R D) := rfl
  rw [h]
  exact BimoduleTensor.composeLeftRestrictionIso R E D D C F
      (BimoduleCategory.of R E D P) (BimoduleCategory.of R D D (Bimodule.diagonal R D)) ≪≫
    (BimoduleCategory.middleLeftRestrictionFunctor R E D C F).mapIso
      (BimoduleTensor.rightBimoduleUnitIso R E D P)
end SerrePositivity.InfinityCategories
