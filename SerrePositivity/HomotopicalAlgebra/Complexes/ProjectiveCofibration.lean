module

public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveModel

/-!
# 射影 cofibration の各次数での分裂

概要：Hovey §2.3 の射影 cofibration は各次数で分裂単射である。
方針：始域を恒等射の非輪状 cone に埋め込み、cone から零への射に持ち上げる。
規約：モデル構造を instance として仮定せず、生成類の左持ち上げ性から導く。
使われ方：余代数区間の境界の前合成による内部 Hom の各次数全射性を示す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.ProjectiveCofibration

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.CochainComplex
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：射影 cofibration の各成分は分裂単射（Hovey §2.3）。
方針：恒等射の cone への延長を持ち上げ性で得て、次数付き右射影を合成する。
規約：分裂の微分との可換性は要求しない。
使われ方：任意の値域複体への内部 Hom の境界制限が各次数で全射となる。 -/
lemma projectiveCofibration_degreewise_isSplitMono {X Y : Complex A} (f : X ⟶ Y)
    (hf : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp f) (n : ℤ) : IsSplitMono (f.f n) := by
  let C := mappingCone (𝟙 X)
  let p : C ⟶ (HomologicalComplex.zero : Complex A) := 0
  have hC : C.Acyclic := (complex_quasiIso_iff_acyclic_cone A (𝟙 X)).1 inferInstance
  have hz (k : ℤ) : IsZero ((HomologicalComplex.zero : Complex A).X k) :=
    (HomologicalComplex.eval (ModuleCat A) (.up ℤ) k).map_isZero HomologicalComplex.isZero_zero
  have hp : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp p := by
    rw [_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations_rlp]
    refine ⟨?_, ?_⟩
    · intro k y
      have := ModuleCat.subsingleton_of_isZero (hz k)
      exact ⟨0, Subsingleton.elim _ _⟩
    · rw [mem_quasiIso_iff, quasiIso_iff]
      intro k
      exact (quasiIsoAt_iff_exactAt p k (hC k)).2 (ExactAt.of_isZero (hz k))
  let sq : CommSq (mappingCone.inr (𝟙 X)) f p
      (0 : Y ⟶ (HomologicalComplex.zero : Complex A)) := ⟨by simp [p]⟩
  obtain ⟨l⟩ := ((hf p hp).sq_hasLift sq).exists_lift
  refine ⟨⟨{
    retraction := l.l.f n ≫ (mappingCone.snd (𝟙 X)).v n n (add_zero n)
    id := ?_ }⟩⟩
  rw [← Category.assoc, ← HomologicalComplex.comp_f, l.fac_left]
  exact mappingCone.inr_f_snd_v (𝟙 X) n

end SerrePositivity.ProjectiveCofibration
