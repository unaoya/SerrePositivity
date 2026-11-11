module
public import SerrePositivity.KST.NonConnective.SequentialCandidateMapExactPi

/-!
概要：n 回 loop した段の非負範囲 j+n の比較を、同じ実候補の全整数 π へ渡す。
方針：次数 j ごとに (-j).toNat 以後を取り、既存の末尾判定を適用する。
規約：実逐次比較を明示入力に取る。loop の次数移動自体は Sp 正本の比較で照合する。
使われ方：K-7 d・e の連結版比較・完全性から同じ非連結化候補への形式部分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
local instance shiftedCandidateSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 概要：各段の移動後非負範囲での π 同型から、同じ実候補比較の全整数 π 同型。
方針：同じ次数 j の十分後の段では j+n が非負となることを使う。
規約：同じ実逐次比較を保持する。使われ方：連結範囲の実比較を非連結化後へ渡す。 -/
theorem sequentialCandidateMap_piIsomorphism_of_nonnegative_shift
    {D E : SpectrumSequence.{u}} (η : D ⟶ E)
    (hη : ∀ (n : ℕ) (j : ℤ), 0 ≤ j + (n : ℤ) →
      Function.Bijective (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j)) :
    OmegaSpectrum.PiIsomorphism (sequentialCandidateMap η) := by
  apply sequentialCandidateMap_piIsomorphism_of_eventually η
  intro j
  refine ⟨(-j).toNat, fun n hn => hη n j ?_⟩
  have hb := Int.self_le_toNat (-j)
  omega

/-- 概要：各段の移動後非負範囲での π 同型から、同じ候補比較の実 Sp 辺は可逆。
方針：元の同じ BF 射の全整数 π 同型を既存の可逆性検出へ渡す。
規約：同じ実辺を保持し、dg Morita 比較の存在は主張しない。
使われ方：K-7 e の実反復比較が供給された後の不変性。 -/
theorem sequentialCandidateMap_isInvertible_of_nonnegative_shift
    {D E : SpectrumSequence.{u}} (η : D ⟶ E)
    (hη : ∀ (n : ℕ) (j : ℤ), 0 ≤ j + (n : ℤ) →
      Function.Bijective (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (sequentialCandidateMap η)) :=
  OmegaSpectrum.isInvertible_of_piIsomorphism _
    (sequentialCandidateMap_piIsomorphism_of_nonnegative_shift η hη)

/-- 概要：各段の移動後非負範囲での核・像一致から、同じ候補比較の全整数 π での完全性。
方針：同じ次数ごとに非負範囲に入る末尾を取り、元の実注入による完全性へ渡す。
規約：実逐次比較対を明示入力とする。Sp fiber 四角形そのものは結論しない。
使われ方：K-7 e の連結版 fibration の群計算を非連結化後へ渡す形式部分。 -/
theorem sequentialCandidateMap_mulExact_of_nonnegative_shift
    {D E F : SpectrumSequence.{u}} (η : D ⟶ E) (θ : E ⟶ F)
    (h : ∀ (n : ℕ) (j : ℤ), 0 ≤ j + (n : ℤ) → Function.MulExact
      (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j)
      (OmegaSpectrum.homotopyMap (θ.app ⟨n⟩) j)) (j : ℤ) :
    Function.MulExact (OmegaSpectrum.homotopyMap (sequentialCandidateMap η) j)
      (OmegaSpectrum.homotopyMap (sequentialCandidateMap θ) j) := by
  apply sequentialCandidateMap_mulExact_of_eventually η θ j (-j).toNat
  intro n hn
  apply h n j
  have hb := Int.self_le_toNat (-j)
  omega

end SerrePositivity.KST.NonConnective
