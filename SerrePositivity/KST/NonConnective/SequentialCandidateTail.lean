module
public import SerrePositivity.KST.NonConnective.SequentialCandidatePi
public import SerrePositivity.KST.NonConnective.SequentialPi

/-!
概要：実逐次 Sp 余錐の十分後の脚を、同じ末尾の隣接射の π 同型性で判定する。
方針：同じ元の隣接射を有限合成して、既存の群余極限の末尾判定へ渡す。
規約：指定次数と指定段に限る。負次数の消滅や全段の安定化を仮定しない。
使われ方：K-7 d3 の採用経路で、同じ非連結化候補の全整数群を段別に表示する。
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 概要：指定段以後の同じ実隣接射が π 同型なら、その段の実余錐の脚も π 同型。
方針：同じ有限合成の作用の全単射性を元の群余極限の末尾判定へ適用する。
規約：元の逐次図式と同じ実 Sp 余錐の脚を保持する。
使われ方：非負範囲へ移動した懸垂段から、同じ候補の任意整数 π への接続。 -/
theorem sequentialCandidateLeg_bijective_of_adjacent_tail
    (D : SpectrumSequence.{u}) (j : ℤ) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n → Function.Bijective (OmegaSpectrum.homotopyMap
      (D.map (homOfLE (X := SequentialIndex.{u}) (Nat.le_succ n))) j)) :
    Function.Bijective (OmegaSpectrum.homotopyMap (sequentialCandidateColimitLegHom D ⟨N⟩) j) := by
  rw [sequentialCandidateColimitLeg_pi]
  apply sequentialInjection_bijective_of_stable D j N
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    have he : (homOfLE (X := SequentialIndex.{u}) (Nat.le_refl N)) =
        𝟙 (⟨N⟩ : SequentialIndex.{u}) := Subsingleton.elim _ _
    rw [he, D.map_id, OmegaSpectrum.homotopyMap_id]
    exact Function.bijective_id
  | succ m hm ih =>
    have he : (homOfLE (X := SequentialIndex.{u}) (Nat.le_succ_of_le hm)) =
        homOfLE (X := SequentialIndex.{u}) hm ≫
          homOfLE (X := SequentialIndex.{u}) (Nat.le_succ m) := Subsingleton.elim _ _
    rw [he, D.map_comp, OmegaSpectrum.homotopyMap_comp]
    exact (h m hm).comp ih

end SerrePositivity.KST.NonConnective
