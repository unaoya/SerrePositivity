module
public import SerrePositivity.KST.NonConnective.DGKappaThomasonCofinality
public import SerrePositivity.KST.NonConnective.SequentialCandidateMapEventualPi

/-!
概要：同じ実逐次比較の段別完備化座標へ Thomason 共終性を代入する。
方針：j+n が厳密に正となる末尾で正次数全単射を使い、同じ候補比較へ渡す。
規約：実逐次比較・元の K 射との座標可換性は明示入力。全入力作用は推論しない。
使われ方：K-7 e の非連結化後の完備化比較。零次全射性を仮定しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
local instance thomasonCandidateSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {D E : SpectrumSequence.{u}} (η : D ⟶ E)
  (X Y : ℕ → StableModel.{u}) (f : ∀ n, X n ⟶ Y n)
  (hf : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion (f n).val)
  (a : ∀ (n : ℕ) (j : ℤ), OmegaSpectrum.homotopyGroup (D.obj ⟨n⟩) j ≃*
    OmegaSpectrum.homotopyGroup (kOmegaSpectrum (X n)) (j + n))
  (b : ∀ (n : ℕ) (j : ℤ), OmegaSpectrum.homotopyGroup (E.obj ⟨n⟩) j ≃*
    OmegaSpectrum.homotopyGroup (kOmegaSpectrum (Y n)) (j + n))
  (h : ∀ (n : ℕ) (j : ℤ) (x : OmegaSpectrum.homotopyGroup (D.obj ⟨n⟩) j),
    b n j (OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j x) =
      OmegaSpectrum.homotopyMap (kSpectrumMap (f n)) (j + n) (a n j x))
include hf h

/-- 概要：元の完備化 K 射と可換な同じ実逐次比較は、候補の全整数 π で同型。
方針：(-j).toNat+1 以後で Thomason の正次数成分を使う。
規約：零次単射を零次全単射として使わない。座標は同じ実 η との可換式を保持する。
使われ方：工程 e の完備化前後の比較を、全整数の同じ実候補へ送る。 -/
theorem sequentialCandidateMap_piIsomorphism_of_thomason :
    OmegaSpectrum.PiIsomorphism (sequentialCandidateMap η) := by
  apply sequentialCandidateMap_piIsomorphism_of_eventually η
  intro j
  refine ⟨(-j).toNat + 1, fun n hn => ?_⟩
  have hj : 0 < j + (n : ℤ) := by
    have hb := Int.self_le_toNat (-j)
    omega
  have hc := (Cofinality.kSpectrumMap_cofinality (f n) (hf n)).1 (j + n) hj
  have he : (b n j) ∘ OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j =
      OmegaSpectrum.homotopyMap (kSpectrumMap (f n)) (j + n) ∘ (a n j) :=
    funext (h n j)
  have ht : Function.Bijective ((b n j) ∘ OmegaSpectrum.homotopyMap (η.app ⟨n⟩) j) := by
    rw [he]
    exact hc.comp (a n j).bijective
  exact ⟨fun _ _ heq => ht.injective (congrArg (b n j) heq), fun y => by
    obtain ⟨x, hx⟩ := ht.surjective (b n j y)
    exact ⟨x, (b n j).injective hx⟩⟩

/-- 同じ候補比較の実 Sp 辺は可逆。dg 入力から実逐次比較の存在は主張しない。 -/
theorem sequentialCandidateMap_isInvertible_of_thomason :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (sequentialCandidateMap η)) :=
  OmegaSpectrum.isInvertible_of_piIsomorphism _
    (sequentialCandidateMap_piIsomorphism_of_thomason η X Y f hf a b h)

end SerrePositivity.KST.NonConnective
