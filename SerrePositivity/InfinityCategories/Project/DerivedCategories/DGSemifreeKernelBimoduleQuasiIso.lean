module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelBimoduleMapPrecomp
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelComparisonInfinity
/-!
概要：同じ双加群射の像と準同型性を、実分解後の可逆性へ接続する。
方針：元の評価射・全 Hom 自然性・型付きの射の一致を保持する。
規約：出力の射影性と原 Hom の平坦性は不要。使われ方：模型変更の全自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E D} (f : P ⟶ Q)
local notation "I" => dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)
local notation "b" => BimoduleTensor.composeMap R E D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) f
  (𝟙 (BimoduleCategory.of R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) I))
lemma dgSemifreeKernelBimoduleMap_evaluation (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (BimoduleCategory.evaluation R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) M).map b =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelMap R D E f M := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelBimoduleMap_precomp_closed R D E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) f I M]
  rfl
lemma dgSemifreeKernelBimoduleMap_quasiIso (hf : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E D f) :
    BimoduleCategory.quasiIso R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) b := by
  intro e M
  change QuasiIso ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R E e).map
    ((BimoduleCategory.evaluation R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) M).map b))
  rw [dgSemifreeKernelBimoduleMap_evaluation]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelMap_quasiIso R D E f hf M e
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
