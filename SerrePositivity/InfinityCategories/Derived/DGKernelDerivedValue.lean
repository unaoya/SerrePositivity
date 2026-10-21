module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedInfinity
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 同じ実切断が入力へ与える半自由 tensor 分解。 -/
def dgKernelDerivedValue (P : Bimodule R E D) (M : SemifreeDGModules R D) :
    SemifreeDGModules R E :=
  dgModuleOutputResolutionValue R (SemifreeDGModules R D) E (dgSemifreeKernelModuleDG R D E P) M
/-- 同じ頂点値から元の同じ tensor への実 augmentation。 -/
def dgKernelDerivedAugmentation (P : Bimodule R E D) (M : SemifreeDGModules R D) :
    ForgetEnrichment.of (Complex R) (dgKernelDerivedValue R D E P M).val ⟶
      ForgetEnrichment.of (Complex R) ((Morita.kernelTensor R D E P).obj M.val) :=
  dgModuleOutputResolutionAugmentation R (SemifreeDGModules R D) E
    (dgSemifreeKernelModuleDG R D E P) M
/-- 同じ実 augmentation は各評価で準同型。 -/
lemma dgKernelDerivedAugmentation_quasiIso (P : Bimodule R E D) (M : SemifreeDGModules R D) :
    moduleQuasiIso R E (dgKernelDerivedAugmentation R D E P M) :=
  dgModuleOutputResolutionAugmentation_quasiIso R (SemifreeDGModules R D) E
    (dgSemifreeKernelModuleDG R D E P) M
/-- 同じ実 augmentation は、各評価の全整数次数で全射。 -/
lemma dgKernelDerivedAugmentation_degree_surjective (P : Bimodule R E D)
    (M : SemifreeDGModules R D) :
    moduleDegreewiseSurjective R E (dgKernelDerivedAugmentation R D E P M) :=
  dgModuleOutputResolutionAugmentation_degree_surjective R (SemifreeDGModules R D) E
    (dgSemifreeKernelModuleDG R D E P) M
/-- 実作用の同じ頂点値は、同じ厳密切断の半自由 tensor 分解そのもの。 -/
lemma dgKernelDerivedInfinity_vertex (P : Bimodule R E D) (M : SemifreeDGModules R D) :
    (dgKernelDerivedInfinity R D E P).app (Opposite.op ⦋0⦌) (Simplex.vertex M) =
      Simplex.vertex (dgKernelDerivedValue R D E P M) := by
  change (dgNerve.map (dgUniverseLiftDown R (SemifreeDGModules R E))).app (Opposite.op ⦋0⦌)
    ((dgModuleOutputResolutionInfinity R (SemifreeDGModules R D) E
      (dgSemifreeKernelModuleDG R D E P)).app (Opposite.op ⦋0⦌) (Simplex.vertex
        ((dgUniverseLiftUp R (SemifreeDGModules R D)).obj M))) = _
  rw [dgModuleOutputResolutionInfinity_vertex]
  rfl
end SerrePositivity.InfinityCategories
