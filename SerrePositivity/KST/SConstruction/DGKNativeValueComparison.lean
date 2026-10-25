module
public import SerrePositivity.KST.SConstruction.DGKFixedInterface
public import SerrePositivity.KST.SConstruction.DGKUniverseQuasiEquivalence
public import SerrePositivity.KST.SConstruction.PerfectDGMoritaEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGPerfectYonedaIdempotentCompletion
public import SerrePositivity.InfinityCategories.Derived.DGNerveUniverseLift
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompleteImageRetracts

/-!
概要：元の小 dg 圏から同じ固定 ν 値への実 Yoneda 比較を与える。
方針：共通宇宙の Yoneda と実 Perf 評価を使い、完備な元圏では同値性を証明する。
規約：元対象と比較関手を保持し、全 Perf の Small 性を要求しない。
使われ方：d④ の native cell・核と固定 ν 値の全図式比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open F2.Idempotent
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type (u + 1))
  [DGCategory R D] [Small.{u} D] [IsDGPretriangulated R D]

/-- 概要：同じ native dg 圏の共通宇宙への実同値。
方針：対象を持ち上げる同じ準同値を使用する。
規約：全 Hom を保持する。使われ方：Yoneda 比較の始域。 -/
def dgKNativeLiftEquivalence : QCatEquivalence (dgNerve R D)
    (dgNerve R (DGUniverseLift.{u + 1, u + 1} D)) :=
  (dgNerve_map_isQCatEquivalence_of_quasiEquivalence
    (dgUniverseLiftUp.{u, u + 1, u + 1} R D)
    (dgKUniverseLiftUp_quasiEquivalence R D)).choose

/-- 概要：同じ固定入力の Perf から元 dg 圏の Perf への指定同値。
方針：実宇宙下降の一回 Perf 延長を使用する。
規約：別の Perf 模型を選ばない。使われ方：固定 ν 比較の終域照合。 -/
def dgKNativePerfectDownEquivalence : QCatEquivalence
    (dgNerve R (PerfectDGModule R (dgKUniverseInput.{u, u + 1, u + 1} R D)))
    (dgNerve R (PerfectDGModule R D)) := by
  let F := dgUniverseLiftDown.{u, u + 1, u + 1} R D
  letI : (quasiEquivalencePerfectExtension R (DGUniverseLift.{u + 1, u + 1} D)
      D F).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence R _ _ F
      (dgKUniverseLiftDown_quasiEquivalence R D)).isEquivalence_functor
  exact (dgNerve_map_isQCatEquivalence_of_quasiEquivalence
    (perfectDGExtension R _ _ F) (perfectDGExtension_quasiEquivalence R _ _ F)).choose

/-- 概要：元の実 Perf から同じ固定 ν 値への同値。
方針：同じ宇宙下降と presented Perf 評価の逆を使用する。
規約：同じ固定入力を保つ。使われ方：native 比較の終域。 -/
def dgKNativePerfectValueEquivalence : QCatEquivalence
    (dgNerve R (PerfectDGModule R D))
    (dgKInputStableValue R (dgKUniverseInput.{u, u + 1, u + 1} R D)).obj :=
  (dgKNativePerfectDownEquivalence R D).symm.trans
    (presentedPerfectDGQCatEvaluationEquivalence R
      (dgKUniverseInput.{u, u + 1, u + 1} R D)).symm

/-- 概要：元 dg 圏の同じ Yoneda を固定 ν 値へ運んだ実比較。
方針：始域・終域の指定同値を合成する。
規約：完備性なしでも同じ比較を定義する。使われ方：native 零化面の照合。 -/
def dgKNativeValueComparison : dgNerve R D ⟶
    (dgKInputStableValue R (dgKUniverseInput.{u, u + 1, u + 1} R D)).obj :=
  (dgKNativeLiftEquivalence R D).hom ≫
    (dgPerfectYonedaInfinity R D ≫ (dgKNativePerfectValueEquivalence R D).hom)

/-- 概要：元 native 圏が coherent 冪等完備なら同じ固定 ν 比較は同値。
方針：D-21 の実 retract を元完備圏の充満忠実像の中で分裂する。
規約：任意の商の strict 局所化を結論しない。使われ方：cell・核の実比較同値。 -/
lemma dgKNativeValueComparison_isQCatEquivalence (hD : IsIdempotentComplete (dgNerve R D)) :
    IsQCatEquivalence (dgKNativeValueComparison R D) := by
  let U := dgKNativeLiftEquivalence R D
  let V := dgKNativePerfectValueEquivalence R D
  let Y := dgPerfectYonedaInfinity R D
  have hY := dgPerfectYonedaInfinity_isIdempotentCompletion R D
  have hL := hD.of_equivalence U
  have hE : IsEssentiallySurjective Y := by
    intro y
    obtain ⟨x, ⟨r⟩⟩ := hY.2.2 y
    obtain ⟨x', ⟨v⟩⟩ := hL.retract_iso_in_image Y hY.2.1 x y r
    exact ⟨x', ⟨v.symm⟩⟩
  have hQ := isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective Y hY.2.1 hE
  exact U.isQCatEquivalence.comp (hQ.comp V.isQCatEquivalence)


/-- 概要：共通宇宙を経由する同じ Yoneda は元の native Yoneda と一致する。
方針：対象の上げ下げを厳密に消去する。規約：全単体の等号。
使われ方：固定 ν 比較を元の Yoneda 自然性へ戻す。 -/
lemma dgKNativeValueComparison_lift_yoneda :
    (dgKNativeLiftEquivalence R D).hom ≫ dgPerfectYonedaInfinity R D =
      dgNerve.map (dgPerfectYoneda R D) := by
  change dgNerve.map (dgUniverseLiftUp.{u, u + 1, u + 1} R D) ≫
    dgNerve.map ((dgUniverseLiftDown.{u, u + 1, u + 1} R D).comp
      (dgPerfectYoneda R D)) = _
  rw [← dgNerve.map_comp]
  congr 1

/-- 概要：同じ固定 ν 比較を元の native Yoneda と終域同値で表示する。
方針：厳密な宇宙回収式を使用する。規約：比較関手を変更しない。
使われ方：全関手自然性を接続する始点。 -/
lemma dgKNativeValueComparison_eq : dgKNativeValueComparison R D =
    dgNerve.map (dgPerfectYoneda R D) ≫ (dgKNativePerfectValueEquivalence R D).hom := by
  unfold dgKNativeValueComparison
  rw [← Category.assoc, dgKNativeValueComparison_lift_yoneda]

/-- 概要：同じ固定 ν 比較は元の native 安定圏からの完全関手。
方針：D の Yoneda の完全性と両指定同値の完全性を合成する。
規約：完備性は仮定しない。使われ方：実零化面の native 頂点比較。 -/
lemma dgKNativeValueComparison_isExact : IsExactFunctor (dgKNativeValueComparison R D) := by
  letI := isExactFunctor_of_isQCatEquivalence
    (dgKNativeLiftEquivalence R D).isQCatEquivalence
  letI := dgPerfectYonedaInfinity_isExactFunctor R D
  letI := isExactFunctor_of_isQCatEquivalence
    (dgKNativePerfectValueEquivalence R D).isQCatEquivalence
  exact isExactFunctor_comp _ _

end SerrePositivity.KST.SConstruction
