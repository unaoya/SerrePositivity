module
public import SerrePositivity.InfinityCategories.Derived.DGKernelBimoduleMapPrecomp
public import SerrePositivity.InfinityCategories.Derived.DGKernelComparisonInfinity
/-!
概要：同じ双加群射の像と準同型性を、実分解後の可逆性へ接続する。
方針：元の評価射・全 Hom 自然性・型付きの射の一致を保持する。
規約：出力の射影性と原 Hom の平坦性は不要。使われ方：模型変更の全自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  {P Q : BimoduleCategory R E D} (f : P ⟶ Q)
local notation "I" => dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D)
local notation "b" => BimoduleTensor.composeMap R E D (SemifreeDGModules R D) f
  (𝟙 (BimoduleCategory.of R D (SemifreeDGModules R D) I))
lemma dgSemifreeKernelBimoduleMap_evaluation (M : SemifreeDGModules R D) :
    (BimoduleCategory.evaluation R E (SemifreeDGModules R D) M).map b =
      dgSemifreeKernelMap R D E f M := by
  rw [dgKernelBimoduleMap_precomp_closed R D E (SemifreeDGModules R D) f I M]
  rfl
lemma dgSemifreeKernelBimoduleMap_quasiIso (hf : BimoduleCategory.quasiIso R E D f) :
    BimoduleCategory.quasiIso R E (SemifreeDGModules R D) b := by
  intro e M
  change QuasiIso ((moduleEvaluation R E e).map
    ((BimoduleCategory.evaluation R E (SemifreeDGModules R D) M).map b))
  rw [dgSemifreeKernelBimoduleMap_evaluation]
  exact dgSemifreeKernelMap_quasiIso R D E f hf M e
end
end SerrePositivity.InfinityCategories
