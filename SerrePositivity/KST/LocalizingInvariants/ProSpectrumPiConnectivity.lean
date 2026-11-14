module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.LocalizingInvariants.ProSpectrumIsoCriterion

/-!
概要：値の塔と射の次数範囲付き π-pro 消滅・核像判定を定義する。
方針：既存の全整数 π の塔を制限し、全範囲の判定との一致を示す。
規約：LT の切断 pro 対象の零性との同定は別工程。使われ方：連結度付き切除の群の界面。
-/

@[expose] public section
universe u
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.ProSpectrum

def IsPiProConnective (X : Tower.{u}) (n : ℤ) : Prop :=
  ∀ j : ℤ, j < n → ProExcision.IsProZero (groups X j)

def IsPiProConnected {X Y : Tower.{u}} (f : LevelHom X Y) (n : ℤ) : Prop :=
  (∀ j : ℤ, j < n → ProGroup.IsEventuallyKernelTrivial (f.map (SpectrumHo.piFunctor j))) ∧
    ∀ j : ℤ, j ≤ n → ProGroup.IsEventuallyImageSurjective (f.map (SpectrumHo.piFunctor j))

lemma IsPiProConnective.mono {X : Tower.{u}} {m n : ℤ}
    (h : IsPiProConnective X n) (hmn : m ≤ n) : IsPiProConnective X m :=
  fun j hj ↦ h j (hj.trans_le hmn)

lemma IsPiProConnected.mono {X Y : Tower.{u}} {f : LevelHom X Y} {m n : ℤ}
    (h : IsPiProConnected f n) (hmn : m ≤ n) : IsPiProConnected f m :=
  ⟨fun j hj ↦ h.1 j (hj.trans_le hmn), fun j hj ↦ h.2 j (hj.trans hmn)⟩

lemma piProZero_iff_forall_connective (X : Tower.{u}) :
    IsPiProZero X ↔ ∀ n : ℤ, IsPiProConnective X n := by
  constructor
  · exact fun h _ j _ ↦ h j
  · exact fun h j ↦ h (j + 1) j (by omega)

lemma piProEquivalence_iff_forall_connected {X Y : Tower.{u}} (f : LevelHom X Y) :
    IsPiProEquivalence f ↔ ∀ n : ℤ, IsPiProConnected f n := by
  rw [piProEquivalence_iff_kernel_image]
  constructor
  · exact fun h n ↦ ⟨fun j _ ↦ (h j).1, fun j _ ↦ (h j).2⟩
  · intro h j
    exact ⟨(h (j + 1)).1 j (by omega), (h j).2 j (le_refl j)⟩

lemma IsPiProConnected.groupMap_isProIso {X Y : Tower.{u}} {f : LevelHom X Y} {n j : ℤ}
    (h : IsPiProConnected f n) (hj : j < n) :
    ProExcision.IsProIso (f.map (SpectrumHo.piFunctor j)) :=
  ProGroup.proIso_of_kernel_image (h.1 j hj) (h.2 j hj.le)

end SerrePositivity.KST.LocalizingInvariants.ProSpectrum

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite LT "Def 2.27" (partial := component) "仮定：自然数塔のレベル射とレベルごとのファイバー列（Lean が強い）。結論：整数次数での弱同値と連結度をプロ群で定義し、ファイバーの消滅と比較。任意の ∞ プロ圏の切断と弱引き戻しの一般定義はない（Lean が弱い）。"] _root_.SerrePositivity.KST.LocalizingInvariants.ProSpectrum.IsPiProConnected
