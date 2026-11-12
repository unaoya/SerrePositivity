module
public import SerrePositivity.KST.NonConnective.SequentialCandidateMapPi
public import SerrePositivity.KST.NonConnective.SequentialPi

/-!
概要：同じ厳密逐次比較の十分後の整数 π 比較から、元の実候補比較を判定する。
方針：元の実注入の可換性と同じ π の十分後の段表示・等号判定を使う。
規約：逐次比較は明示入力。dg 入力自然性・Morita 列比較の存在は主張しない。
使われ方：K-7 d・e の比較で、初期の有限段の相違を避けて同じ実候補を照合する。
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
local instance eventualCandidateSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 概要：十分後の各段で単射な同じ逐次比較は、元の候補の同じ整数 π でも単射。
方針：核の元を十分後で表示し、像の消滅をさらに後の同じ遷移で回収する。
規約：元の実比較と実注入を保持する。使われ方：候補比較の単射性の末尾判定。 -/
theorem sequentialCandidateMap_pi_injective_of_eventually
    {D E : SpectrumSequence.{u}} (η : D ⟶ E) (j : ℤ) (N : ℕ)
    (hη : ∀ n : ℕ, N ≤ n → Function.Injective (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j)) :
    Function.Injective (OmegaSpectrum.homotopyMap (sequentialCandidateMap η) j) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  obtain ⟨n, hn, x, hx⟩ := sequentialPi_exists_late D j N a
  have hc := DFunLike.congr_fun (sequentialCandidateMap_pi_injection η ⟨n⟩ j) x
  change OmegaSpectrum.homotopyMap (sequentialCandidateMap η) j
      (OmegaSpectrum.homotopyMap (sequentialInjection D n) j x) =
    OmegaSpectrum.homotopyMap (sequentialInjection E n) j
      (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j x) at hc
  have hz : OmegaSpectrum.homotopyMap (sequentialInjection E n) j
      (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j x) = 1 :=
    hc.symm.trans ((congrArg (OmegaSpectrum.homotopyMap (sequentialCandidateMap η) j) hx).trans ha)
  obtain ⟨m, hnm, hm⟩ := (sequentialPi_eq_one_iff E j n _).mp hz
  have hw := congrArg (fun f => OmegaSpectrum.homotopyMap f j)
    (η.naturality (homOfLE (X := SequentialIndex.{u}) hnm))
  rw [OmegaSpectrum.homotopyMap_comp, OmegaSpectrum.homotopyMap_comp] at hw
  have he := DFunLike.congr_fun hw x
  change OmegaSpectrum.homotopyMap (η.app ⟨m⟩) j
      (OmegaSpectrum.homotopyMap (D.map (homOfLE hnm)) j x) =
    OmegaSpectrum.homotopyMap (E.map (homOfLE hnm)) j
      (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j x) at he
  have hxone : OmegaSpectrum.homotopyMap (D.map (homOfLE hnm)) j x = 1 := by
    apply hη m (hn.trans hnm)
    simpa only [map_one] using he.trans hm
  exact hx.symm.trans ((sequentialPi_eq_one_iff D j n x).mpr ⟨m, hnm, hxone⟩)

/-- 概要：十分後の各段で全射な同じ逐次比較は、元の候補の同じ整数 π でも全射。
方針：任意の像を十分後で表示し、その段の原像を同じ実注入で送る。
規約：元の実余錐の脚を保持する。使われ方：候補比較の全射性の末尾判定。 -/
theorem sequentialCandidateMap_pi_surjective_of_eventually
    {D E : SpectrumSequence.{u}} (η : D ⟶ E) (j : ℤ) (N : ℕ)
    (hη : ∀ n : ℕ, N ≤ n → Function.Surjective (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j)) :
    Function.Surjective (OmegaSpectrum.homotopyMap (sequentialCandidateMap η) j) := by
  intro b
  obtain ⟨n, hn, y, hy⟩ := sequentialPi_exists_late E j N b
  obtain ⟨x, hx⟩ := hη n hn y
  refine ⟨OmegaSpectrum.homotopyMap (sequentialInjection D n) j x, ?_⟩
  have hc := DFunLike.congr_fun (sequentialCandidateMap_pi_injection η ⟨n⟩ j) x
  change OmegaSpectrum.homotopyMap (sequentialCandidateMap η) j
      (OmegaSpectrum.homotopyMap (sequentialInjection D n) j x) =
    OmegaSpectrum.homotopyMap (sequentialInjection E n) j
      (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j x) at hc
  exact hc.trans ((congrArg (OmegaSpectrum.homotopyMap (sequentialInjection E n) j) hx).trans hy)

/-- 概要：同じ逐次比較は指定次数で十分後の各段が全単射なら候補でも全単射。
方針：同じ実候補比較の末尾単射・全射判定を合わせる。
規約：遷移射自身の安定性を追加仮定にしない。
使われ方：K-7 の実列比較を同じ候補へ送る。 -/
theorem sequentialCandidateMap_pi_bijective_of_eventually
    {D E : SpectrumSequence.{u}} (η : D ⟶ E) (j : ℤ) (N : ℕ)
    (hη : ∀ n : ℕ, N ≤ n → Function.Bijective (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j)) :
    Function.Bijective (OmegaSpectrum.homotopyMap (sequentialCandidateMap η) j) :=
  ⟨sequentialCandidateMap_pi_injective_of_eventually η j N (fun n hn => (hη n hn).injective),
    sequentialCandidateMap_pi_surjective_of_eventually η j N (fun n hn => (hη n hn).surjective)⟩

/-- 概要：次数ごとに十分後の段で π 同型なら、同じ実候補比較は全整数で π 同型。
方針：元の同じ実比較を各次数の末尾判定へ代入する。
規約：次数と独立の一様な末尾は要求しない。
使われ方：同じ非連結化候補の比較同値の形式部分。 -/
theorem sequentialCandidateMap_piIsomorphism_of_eventually
    {D E : SpectrumSequence.{u}} (η : D ⟶ E)
    (hη : ∀ j : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Function.Bijective (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j)) :
    OmegaSpectrum.PiIsomorphism (sequentialCandidateMap η) := by
  intro j
  obtain ⟨N, hN⟩ := hη j
  exact sequentialCandidateMap_pi_bijective_of_eventually η j N hN

/-- 概要：同じ実逐次比較の十分後の π 同型から、候補比較の実 Sp 辺が可逆。
方針：同じ BF 射の全整数 π 同型を Sp 正本の可逆性検出へ渡す。
規約：元の実辺を保持し、dg 入力作用の存在は仮定しない。
使われ方：K-7 e の実列比較が届いた後の候補不変性。 -/
theorem sequentialCandidateMap_isInvertible_of_eventually
    {D E : SpectrumSequence.{u}} (η : D ⟶ E)
    (hη : ∀ j : ℤ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Function.Bijective (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (sequentialCandidateMap η)) :=
  OmegaSpectrum.isInvertible_of_piIsomorphism _
    (sequentialCandidateMap_piIsomorphism_of_eventually η hη)

end SerrePositivity.KST.NonConnective
