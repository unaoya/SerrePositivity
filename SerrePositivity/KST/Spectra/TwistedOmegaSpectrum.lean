module

public import SerrePositivity.KST.Spectra.TwistedKanSequence
public import SerrePositivity.KST.Spectra.CofibrantSequenceLifting
public import SerrePositivity.KST.Spectra.CofibrantOmegaSequence
public import SerrePositivity.KST.Spectra.SpectrumHomotopyEquivalences

/-!
概要：全基点 π_* 同型の自己射による構造射の変更を BF 対象として比較する。
方針：変更後の Ω 列を cofibrant に置換し、元の単射構造射を用いて比較を持ち上げる。
規約：変更後の構造射の単射性を仮定しない。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。符号を変えた loop 模型の実際の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : OmegaSpectrum.{u}) (r : KanSequence.Hom X.toKanSequence X.toKanSequence)
  (hr : ∀ k, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (r.app k).right)

/-- 概要：自己射の後合成で構造射を変えた BF Ω スペクトル。
方針：変更後の Kan Ω 列を単射構造射へ置換する。
規約：自己射は各段で全基点の π_* 同型。
使われ方：BF 1978 §2、HTT A.3.3。符号変更の BF 対象。 -/
def twisted : OmegaSpectrum.{u} :=
  KanSequence.cofibrantOmegaSpectrum (KanSequence.twist r)
    (KanSequence.twist_omegaCondition r X.toKanSequence_omega hr)

/-- 概要：変更後の BF 対象から変更した Kan 列への比較。
方針：cofibrant 置換の厳密な比較射を使う。
規約：全ての段で単射への RLP を持つ。
使われ方：BF 1978 §2、HTT A.3.3。元の対象からの比較射の持ち上げ。 -/
def twistedProjection : KanSequence.Hom (twisted X r hr).toKanSequence (KanSequence.twist r) :=
  KanSequence.cofibrantOmegaProjection _ _

/-- 概要：元の BF 対象から構造射を変えた BF 対象への厳密な射。
方針：段ごとの反復の比較射を cofibrant 置換の比較射へ持ち上げる。
規約：持ち上げは源の単射な構造射と標的の RLP から実際に構成する。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。符号変更の実際の比較射。 -/
def twistComparison : X ⟶ twisted X r hr := by
  let f := KanSequence.liftHom (X := X.toKanSequence)
    (W := (twisted X r hr).toKanSequence) (Z := KanSequence.twist r) X.sigma_mono
      (twistedProjection X r hr)
      (fun n => (KanSequence.replacementStage (KanSequence.twist r) n).projection_rlp)
      (KanSequence.twistMap r)
  exact { app := f.app, comm := f.comm }

/-- 概要：変更後の BF 比較を忘れると段ごとの反復の射に一致する。
方針：列の持ち上げの比較式を使う。
規約：点つき射の厳密な等式。
使われ方：BF 1978 §2、HA §1.4.2。比較射の各段での同型性の検査。 -/
theorem twistComparison_projection (k : ℕ) :
    (twistComparison X r hr).app k ≫ (twistedProjection X r hr).app k =
      (KanSequence.twistMap r).app k :=
  KanSequence.liftHom_fac (X := X.toKanSequence)
    (W := (twisted X r hr).toKanSequence) (Z := KanSequence.twist r) X.sigma_mono
      (twistedProjection X r hr)
      (fun n => (KanSequence.replacementStage (KanSequence.twist r) n).projection_rlp)
      (KanSequence.twistMap r) k

/-- 概要：構造射を変える BF 比較射は各段で全基点の π_* 同型。
方針：反復の比較の同型性から cofibrant 置換の比較の同型性を打ち消す。
規約：全自然数次数と全ての基点。
使われ方：Goerss–Jardine I §7、BF 1978 §2。符号変更による群の保存。 -/
theorem twistComparison_levelwise (k : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((twistComparison X r hr).app k).right := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := ((twistedProjection X r hr).app k).right) _
    (KanSequence.replacementProjection_piIsomorphism (KanSequence.twist r) k)
  have h := congrArg Under.Hom.right (twistComparison_projection X r hr k)
  change ((twistComparison X r hr).app k).right ≫
      ((twistedProjection X r hr).app k).right = ((KanSequence.twistMap r).app k).right at h
  rw [h]
  exact KanSequence.twistMap_piIsomorphism r hr k

/-- 概要：構造射を変える BF 比較射は全整数次数の π_* 同型。
方針：各段での全基点の同型性を整数次数へ移す。
規約：coherent nerve の同値との比較はここでは主張しない。
使われ方：BF 1978 §2、HA §1.4.2。符号を変えた loop 模型の比較。 -/
theorem twistComparison_piIsomorphism : PiIsomorphism (twistComparison X r hr) :=
  piIsomorphism_of_levelwise _ (twistComparison_levelwise X r hr)

end

end SerrePositivity.KST.Spectra.OmegaSpectrum
