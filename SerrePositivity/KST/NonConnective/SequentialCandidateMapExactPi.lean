module
public import SerrePositivity.KST.NonConnective.SequentialCandidateMapEventualPi
public import Mathlib.Algebra.Exact.Basic

/-!
概要：十分後の段ごとの整数 π の核・像一致を、同じ実逐次候補比較へ渡す。
方針：元の実注入の可換性と、同じ filtered 群余極限の段表示・等号判定を使う。
規約：実逐次比較を明示入力に取り、Sp fiber 四角形や dg Verdier 作用の存在を結論しない。
使われ方：K-7 e の実比較列が供給された後の、同じ候補の整数群での完全性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective

/-- 概要：十分後の各段での核・像一致は、同じ候補比較の同じ整数 π でも成立する。
方針：核の元を十分後で表示し、像の零性を後の段へ移して段別完全性を使う。
規約：元の実列・比較・余錐の脚を保持し、全段での完全性は要求しない。
使われ方：非連結化後の fiber 性を判定する際の群計算の形式部分。 -/
theorem sequentialCandidateMap_mulExact_of_eventually
    {D E F : SpectrumSequence.{u}} (η : D ⟶ E) (θ : E ⟶ F) (j : ℤ) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n → Function.MulExact
      (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j)
      (OmegaSpectrum.homotopyMap (θ.app ⟨n⟩) j)) :
    Function.MulExact (OmegaSpectrum.homotopyMap (sequentialCandidateMap η) j)
      (OmegaSpectrum.homotopyMap (sequentialCandidateMap θ) j) := by
  intro y
  constructor
  · intro hzy
    obtain ⟨n, hn, x, hx⟩ := sequentialPi_exists_late E j N y
    have hc := DFunLike.congr_fun (sequentialCandidateMap_pi_injection θ ⟨n⟩ j) x
    change OmegaSpectrum.homotopyMap (sequentialCandidateMap θ) j
        (OmegaSpectrum.homotopyMap (sequentialInjection E n) j x) =
      OmegaSpectrum.homotopyMap (sequentialInjection F n) j
        (OmegaSpectrum.homotopyMap (θ.app ⟨n⟩) j x) at hc
    have hz : OmegaSpectrum.homotopyMap (sequentialInjection F n) j
        (OmegaSpectrum.homotopyMap (θ.app ⟨n⟩) j x) = 1 :=
      hc.symm.trans ((congrArg (OmegaSpectrum.homotopyMap (sequentialCandidateMap θ) j) hx).trans hzy)
    obtain ⟨m, hnm, hm⟩ := (sequentialPi_eq_one_iff F j n _).mp hz
    have hw := congrArg (fun f => OmegaSpectrum.homotopyMap f j)
      (θ.naturality (homOfLE (X := SequentialIndex.{u}) hnm))
    rw [OmegaSpectrum.homotopyMap_comp, OmegaSpectrum.homotopyMap_comp] at hw
    have he := DFunLike.congr_fun hw x
    change OmegaSpectrum.homotopyMap (θ.app ⟨m⟩) j
        (OmegaSpectrum.homotopyMap (E.map (homOfLE hnm)) j x) =
      OmegaSpectrum.homotopyMap (F.map (homOfLE hnm)) j
        (OmegaSpectrum.homotopyMap (θ.app ⟨n⟩) j x) at he
    obtain ⟨z, hz⟩ := (h m (hn.trans hnm) _).mp (he.trans hm)
    refine ⟨OmegaSpectrum.homotopyMap (sequentialInjection D m) j z, ?_⟩
    have hη := DFunLike.congr_fun (sequentialCandidateMap_pi_injection η ⟨m⟩ j) z
    change OmegaSpectrum.homotopyMap (sequentialCandidateMap η) j
        (OmegaSpectrum.homotopyMap (sequentialInjection D m) j z) =
      OmegaSpectrum.homotopyMap (sequentialInjection E m) j
        (OmegaSpectrum.homotopyMap (η.app ⟨m⟩) j z) at hη
    have hi := ConcreteCategory.congr_hom ((sequentialPiCocone E j).w
      (homOfLE (X := SequentialIndex.{u}) hnm)) x
    change OmegaSpectrum.homotopyMap (sequentialInjection E m) j
        (OmegaSpectrum.homotopyMap (E.map (homOfLE hnm)) j x) =
      OmegaSpectrum.homotopyMap (sequentialInjection E n) j x at hi
    exact hη.trans ((congrArg (OmegaSpectrum.homotopyMap (sequentialInjection E m) j) hz).trans
      (hi.trans hx))
  · rintro ⟨a, rfl⟩
    obtain ⟨n, hn, x, hx⟩ := sequentialPi_exists_late D j N a
    have hη := DFunLike.congr_fun (sequentialCandidateMap_pi_injection η ⟨n⟩ j) x
    change OmegaSpectrum.homotopyMap (sequentialCandidateMap η) j
        (OmegaSpectrum.homotopyMap (sequentialInjection D n) j x) =
      OmegaSpectrum.homotopyMap (sequentialInjection E n) j
        (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j x) at hη
    have hθ := DFunLike.congr_fun (sequentialCandidateMap_pi_injection θ ⟨n⟩ j)
      (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j x)
    change OmegaSpectrum.homotopyMap (sequentialCandidateMap θ) j
        (OmegaSpectrum.homotopyMap (sequentialInjection E n) j
          (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j x)) =
      OmegaSpectrum.homotopyMap (sequentialInjection F n) j
        (OmegaSpectrum.homotopyMap (θ.app ⟨n⟩) j
          (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j x)) at hθ
    have h0 : OmegaSpectrum.homotopyMap (sequentialCandidateMap η) j a =
        OmegaSpectrum.homotopyMap (sequentialInjection E n) j
          (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j x) :=
      (congrArg (OmegaSpectrum.homotopyMap (sequentialCandidateMap η) j) hx.symm).trans hη
    have hz := (h n hn).apply_apply_eq_one x
    exact (congrArg (OmegaSpectrum.homotopyMap (sequentialCandidateMap θ) j) h0).trans
      (hθ.trans ((congrArg (OmegaSpectrum.homotopyMap (sequentialInjection F n) j) hz).trans
        (map_one _)))

end SerrePositivity.KST.NonConnective
