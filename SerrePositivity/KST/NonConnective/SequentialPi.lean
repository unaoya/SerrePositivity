module

public import SerrePositivity.KST.NonConnective.SequentialSpectrum
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
概要：逐次 BF 候補の整数 π の元を十分後の段で表示し、等号を段で判定する。
方針：同じ群 cocone の台集合の filtered 余極限性を使う。
規約：これらの計算から Sp の ∞ 余極限性は結論しない。
使われ方：K-7 の負次数の計算・連結 K との比較の準備。
-/

@[expose] public section

universe u

open CategoryTheory Limits
open SerrePositivity.KST.Spectra

namespace SerrePositivity.KST.NonConnective

noncomputable section

/-- 概要：候補の整数 π の任意の元は指定した段以降で表示できる。
方針：集合余極限の全射性で表示し、添字の max へ送る。
規約：次数と下限の双方を任意に指定できる。
使われ方：非負次数比較の安定範囲への移動。 -/
theorem sequentialPi_exists_late (D : SpectrumSequence.{u}) (j : ℤ) (N : ℕ)
    (x : OmegaSpectrum.homotopyGroup (sequentialSpectrum D) j) :
    ∃ (n : ℕ) (_ : N ≤ n) (y : OmegaSpectrum.homotopyGroup (D.obj ⟨n⟩) j),
      OmegaSpectrum.homotopyMap (sequentialInjection D n) j y = x := by
  obtain ⟨a, y, hy⟩ := Types.jointly_surjective_of_isColimit
    (sequentialPiUnderlyingIsColimit D j) x
  let b : SequentialIndex.{u} := ⟨max a.down N⟩
  let f : a ⟶ b := homOfLE (Nat.le_max_left a.down N)
  refine ⟨b.down, Nat.le_max_right _ _, OmegaSpectrum.homotopyMap (D.map f) j y, ?_⟩
  have hw := ConcreteCategory.congr_hom ((sequentialPiCocone D j).w f) y
  exact hw.trans hy

/-- 概要：同じ段の二つの元が候補で一致する条件。
方針：filtered 集合余極限の等号判定を同じ π cocone に適用する。
規約：元の遷移射による一致を要求する。
使われ方：比較射の単射性と負次数の消滅判定。 -/
theorem sequentialPi_eq_iff (D : SpectrumSequence.{u}) (j : ℤ) (n : ℕ)
    (x y : OmegaSpectrum.homotopyGroup (D.obj ⟨n⟩) j) :
    OmegaSpectrum.homotopyMap (sequentialInjection D n) j x =
        OmegaSpectrum.homotopyMap (sequentialInjection D n) j y ↔
      ∃ (m : ℕ) (h : n ≤ m),
        OmegaSpectrum.homotopyMap (D.map (homOfLE h)) j x =
          OmegaSpectrum.homotopyMap (D.map (homOfLE h)) j y := by
  have he := Types.FilteredColimit.isColimit_eq_iff'
    (sequentialPiUnderlyingIsColimit D j) x y
  change OmegaSpectrum.homotopyMap (sequentialInjection D n) j x =
    OmegaSpectrum.homotopyMap (sequentialInjection D n) j y ↔
    ∃ (m : SequentialIndex.{u}) (f : (⟨n⟩ : SequentialIndex.{u}) ⟶ m),
    OmegaSpectrum.homotopyMap (D.map f) j x = OmegaSpectrum.homotopyMap (D.map f) j y at he
  rw [he]
  constructor
  · rintro ⟨m, f, hf⟩
    exact ⟨m.down, leOfHom (X := SequentialIndex.{u}) f, hf⟩
  · rintro ⟨m, h, hm⟩
    exact ⟨⟨m⟩, homOfLE h, hm⟩

/-- 概要：同じ段からの全遷移が指定次数で全単射なら、その段と BF 候補の π は全単射。
方針：単射性は段での等号判定、全射性は十分後の段での表示による。
規約：安定化を明示の仮定とし、K の安定化定理とは区別する。
使われ方：連結 K との比較の次数別入口。 -/
theorem sequentialInjection_bijective_of_stable (D : SpectrumSequence.{u}) (j : ℤ) (N : ℕ)
    (h : ∀ (m : ℕ) (hm : N ≤ m), Function.Bijective
      (OmegaSpectrum.homotopyMap (D.map (homOfLE hm)) j)) :
    Function.Bijective (OmegaSpectrum.homotopyMap (sequentialInjection D N) j) := by
  constructor
  · intro x y hxy
    obtain ⟨m, hm, he⟩ := (sequentialPi_eq_iff D j N x y).mp hxy
    exact (h m hm).injective he
  · intro x
    obtain ⟨m, hm, y, hy⟩ := sequentialPi_exists_late D j N x
    obtain ⟨z, hz⟩ := (h m hm).surjective y
    refine ⟨z, ?_⟩
    have hw := ConcreteCategory.congr_hom
      ((sequentialPiCocone D j).w (homOfLE hm)) z
    change OmegaSpectrum.homotopyMap (sequentialInjection D m) j
      (OmegaSpectrum.homotopyMap (D.map (homOfLE hm)) j z) =
        OmegaSpectrum.homotopyMap (sequentialInjection D N) j z at hw
    rw [hz, hy] at hw
    exact hw.symm

/-- 概要：候補で単位元になる条件は、後の段で単位元になること。
方針：同じ段の等号判定に群の単位元を代入する。
規約：全整数次数で元ごとに後の段を選ぶ。
使われ方：負次数消滅の判定。 -/
theorem sequentialPi_eq_one_iff (D : SpectrumSequence.{u}) (j : ℤ) (n : ℕ)
    (x : OmegaSpectrum.homotopyGroup (D.obj ⟨n⟩) j) :
    OmegaSpectrum.homotopyMap (sequentialInjection D n) j x = 1 ↔
      ∃ (m : ℕ) (h : n ≤ m),
        OmegaSpectrum.homotopyMap (D.map (homOfLE h)) j x = 1 := by
  simpa only [map_one] using sequentialPi_eq_iff D j n x 1

/-- 概要：候補の π が消滅することと、各元が後の段で消えることは同値。
方針：段での単位元判定と任意の元の段表示を組み合わせる。
規約：一様な消滅段は要求しない。
使われ方：非連結 K の次数別消滅の入口。 -/
theorem sequentialPi_subsingleton_iff (D : SpectrumSequence.{u}) (j : ℤ) :
    Subsingleton (OmegaSpectrum.homotopyGroup (sequentialSpectrum D) j) ↔
      ∀ (n : ℕ) (x : OmegaSpectrum.homotopyGroup (D.obj ⟨n⟩) j),
        ∃ (m : ℕ) (h : n ≤ m),
          OmegaSpectrum.homotopyMap (D.map (homOfLE h)) j x = 1 := by
  constructor
  · intro hs n x
    exact (sequentialPi_eq_one_iff D j n x).mp (hs.elim _ _)
  · intro h
    have hone : ∀ x : OmegaSpectrum.homotopyGroup (sequentialSpectrum D) j, x = 1 := by
      intro x
      obtain ⟨n, _, y, hy⟩ := sequentialPi_exists_late D j 0 x
      rw [← hy]
      exact (sequentialPi_eq_one_iff D j n y).mpr (h n y)
    exact ⟨fun x y ↦ (hone x).trans (hone y).symm⟩

/-- 概要：指定次数の群が十分後の各段で消滅すれば BF 候補でも消滅する。
方針：任意の元を消滅範囲で表示する。
規約：下限 N は次数ごとに変えてよい。
使われ方：後続の dg 懸垂列の消滅範囲との接続。 -/
theorem sequentialPi_subsingleton_of_eventually (D : SpectrumSequence.{u}) (j : ℤ)
    (N : ℕ) (h : ∀ (n : ℕ), N ≤ n →
      Subsingleton (OmegaSpectrum.homotopyGroup (D.obj ⟨n⟩) j)) :
    Subsingleton (OmegaSpectrum.homotopyGroup (sequentialSpectrum D) j) := by
  have hone : ∀ x : OmegaSpectrum.homotopyGroup (sequentialSpectrum D) j, x = 1 := by
    intro x
    obtain ⟨n, hn, y, hy⟩ := sequentialPi_exists_late D j N x
    rw [← hy, (h n hn).elim y 1, map_one]
  exact ⟨fun x y ↦ (hone x).trans (hone y).symm⟩

end

end SerrePositivity.KST.NonConnective
