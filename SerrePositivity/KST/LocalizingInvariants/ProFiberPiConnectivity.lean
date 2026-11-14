module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.LocalizingInvariants.ProGroupFiveTermZero
public import SerrePositivity.KST.LocalizingInvariants.ProSpectrumPiConnectivity
public import SerrePositivity.KST.LocalizingInvariants.ProFiberConnecting

/-!
概要：実 fiber 図式の塔に対し、次数範囲付き π-pro 消滅と射影の核・像条件を同定する。
方針：自然な長完全列の三箇所の完全性と、五項完全列の pro 零判定を使う。
規約：一般 pro ∞ 圏の切断は仮定しない。使われ方：連結度付き切除の群の判定。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.ProFiberSequence

variable (D : ProFiberSequence.{u})

lemma projection_image_surjective_succ (j : ℤ)
    (hF : ProExcision.IsProZero (groups D 0 0 j)) :
    ProGroup.IsEventuallyImageSurjective (groupProjection D (j + 1)) :=
  ProGroup.eventuallyImageSurjective_of_exact_proZero (groupProjection D (j + 1))
    (connectingHom D j) (fun n x ↦ exact_base D n j x) hF

lemma projection_piProConnected {n : ℤ}
    (hF : ProSpectrum.IsPiProConnective (vertex D 0 0) n) :
    ProSpectrum.IsPiProConnected (projection D) n := by
  constructor
  · intro j hj
    exact ProGroup.eventuallyKernelTrivial_of_exact_proZero
      (groupInclusion D j) (groupProjection D j) (fun m x ↦ exact_total D m j x) (hF j hj)
  · intro j hj
    have hp := projection_image_surjective_succ D (j - 1) (hF (j - 1) (by omega))
    have he : j - 1 + 1 = j := by omega
    rw [he] at hp
    exact hp

lemma fiber_piProConnective {n : ℤ}
    (h : ProSpectrum.IsPiProConnected (projection D) n) :
    ProSpectrum.IsPiProConnective (vertex D 0 0) n := by
  intro j hj
  exact ProGroup.proZero_of_fiveTerm_exact (groupProjection D (j + 1)) (connectingHom D j)
    (groupInclusion D j) (groupProjection D j)
    (fun m x ↦ exact_base D m j x) (fun m x ↦ exact_fiber D m j x)
    (fun m x ↦ exact_total D m j x) (h.2 (j + 1) (by omega)) (h.1 j hj)

lemma piConnective_iff_projection_connected (n : ℤ) :
    ProSpectrum.IsPiProConnective (vertex D 0 0) n ↔
      ProSpectrum.IsPiProConnected (projection D) n :=
  ⟨projection_piProConnected D, fiber_piProConnective D⟩

lemma piProZero_iff_projection_piProEquivalence :
    ProSpectrum.IsPiProZero (vertex D 0 0) ↔
      ProSpectrum.IsPiProEquivalence (projection D) := by
  rw [ProSpectrum.piProZero_iff_forall_connective,
    ProSpectrum.piProEquivalence_iff_forall_connected]
  exact forall_congr' (piConnective_iff_projection_connected D)

end SerrePositivity.KST.LocalizingInvariants.ProFiberSequence

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Lemma 4.6" (partial := component) "仮定：レベルのファイバー比較または既に与えたファイバー列（Lean が強い）。結論：比較がプロ同値であるという判定界面と、ファイバーのプロ連結度の群による比較。正方形の合成と実ホモトピー引き戻しの同値は供給しない（Lean が弱い）。"] _root_.SerrePositivity.KST.LocalizingInvariants.ProFiberSequence.piConnective_iff_projection_connected
attribute [cite LT "Def 2.27" (partial := component) "仮定：自然数塔のレベル射とレベルごとのファイバー列（Lean が強い）。結論：整数次数での弱同値と連結度をプロ群で定義し、ファイバーの消滅と比較。任意の ∞ プロ圏の切断と弱引き戻しの一般定義はない（Lean が弱い）。"] _root_.SerrePositivity.KST.LocalizingInvariants.ProFiberSequence.piConnective_iff_projection_connected
attribute [cite LT "Rem 2.3" (partial := component) "仮定：レベルごとのファイバー列の塔と整数係数（Lean が強い）。結論：プロホモトピー群の完全性からファイバーと射の連結度を比較。Λ 係数の四角形の MV 列を直接与えない（Lean が弱い）。"] _root_.SerrePositivity.KST.LocalizingInvariants.ProFiberSequence.piConnective_iff_projection_connected
