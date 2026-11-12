module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelDerivedInfinity
/-!
概要：一般双加群作用の実頂点値と元の tensor への実 augmentation を回収する。
方針：同じ厳密切断から半自由分解・準同型・次数別全射性を読む。
規約：同じ元の入力と同じ tensor を保持する。使われ方：一般 Morita 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 同じ実切断が入力へ与える半自由 tensor 分解。 -/
def dgKernelDerivedValue (P : Bimodule R E D) (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionValue R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P) M
/-- 同じ頂点値から元の同じ tensor への実 augmentation。 -/
def dgKernelDerivedAugmentation (P : Bimodule R E D) (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgKernelDerivedValue R D E P M).val ⟶
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) ((_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D E P).obj M.val) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionAugmentation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P) M
/-- 同じ実 augmentation は各評価で準同型。 -/
lemma dgKernelDerivedAugmentation_quasiIso (P : Bimodule R E D) (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R E (dgKernelDerivedAugmentation R D E P M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionAugmentation_quasiIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P) M
/-- 同じ実 augmentation は、各評価の全整数次数で全射。 -/
lemma dgKernelDerivedAugmentation_degree_surjective (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D)
    (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.DifferentialGraded.moduleDegreewiseSurjective R E (dgKernelDerivedAugmentation R D E P M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionAugmentation_degree_surjective R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P) M
/-- 実作用の同じ頂点値は、同じ厳密切断の半自由 tensor 分解そのもの。 -/
lemma dgKernelDerivedInfinity_vertex (P : Bimodule R E D) (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (dgKernelDerivedValue R D E P M) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E))).app (Opposite.op ⦋0⦌)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P)).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).obj M))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity_vertex]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
