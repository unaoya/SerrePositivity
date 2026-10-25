module
public import SerrePositivity.KST.SConstruction.KHomotopyStageIso

/-!
概要：元の K 射の整数次数での全単射性を、未置換の元の S• の段で検査する。
方針：既存の任意段表示と単射置換射影の自然同型を、同じ指定射に適用する。
規約：実現比較そのものの全同値を追加仮定しない。
使われ方：共終性の S• 直接証明を元の kSpectrumMap へ戻す検出境界。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet Spectra

/-- 概要：同じ実 K 射の整数次数全単射性は任意の許される未置換段で判定できる。
方針：段表示の自然同型の前後で同型性を輸送する。
規約：同じ f の実スペクトル射を使い、別の比較射へ置き換えない。
使われ方：共終性の高次群比較の元の K 射への照合。 -/
theorem kSpectrumMap_bijective_iff_rawStage {X Y : StableModel.{u}} (f : X ⟶ Y)
    (j : ℤ) (k : ℕ) (hk : -j ≤ (k : ℤ)) :
    Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j) ↔
      Function.Bijective ((rawKStageHomotopyFunctor k (OmegaSpectrum.degree j k)).map f) := by
  have h := NatIso.isIso_map_iff (kHomotopyRawStageIso j k hk) f
  rw [ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective] at h
  exact h

/-- 概要：同じ実 K 射の単射性も任意の許される未置換段で検査できる。
方針：段表示の全自然性と両端の集合同値で単射性を両方向に輸送する。
規約：零次の全射性を要求しない。
使われ方：共終性の零次単射性を元の K 空間で検査する。 -/
theorem kSpectrumMap_injective_iff_rawStage {X Y : StableModel.{u}} (f : X ⟶ Y)
    (j : ℤ) (k : ℕ) (hk : -j ≤ (k : ℤ)) :
    Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j) ↔
      Function.Injective ((rawKStageHomotopyFunctor k (OmegaSpectrum.degree j k)).map f) := by
  let e := kHomotopyRawStageIso j k hk
  let eX := (e.app X).toEquiv
  let eY := (e.app Y).toEquiv
  have he (a : OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) j) :
      eY (OmegaSpectrum.homotopyMap (kSpectrumMap f) j a) =
        (rawKStageHomotopyFunctor k (OmegaSpectrum.degree j k)).map f (eX a) :=
    ConcreteCategory.congr_hom (e.hom.naturality f) a
  constructor
  · intro h a b hab
    obtain ⟨a, rfl⟩ := eX.surjective a
    obtain ⟨b, rfl⟩ := eX.surjective b
    apply congrArg eX
    apply h
    apply eY.injective
    exact (he a).trans (hab.trans (he b).symm)
  · intro h a b hab
    apply eX.injective
    apply h
    exact (he a).symm.trans ((congrArg eY hab).trans (he b))

/-- 概要：共終性の求める整数群条件は元の零段の高次全単射性と零次単射性に同値。
方針：全非負整数次数を許される零段へ移し、自然数と整数の次数を照合する。
規約：元の boundary K 空間を使い、完備化射の同値性を要求しない。
使われ方：有限 S 図式による直接証明が満たすべき元の K 射の検査条件。 -/
theorem kSpectrumMap_cofinality_iff_boundary {X Y : StableModel.{u}} (f : X ⟶ Y) :
    ((∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
      Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0)) ↔
    ((∀ n : ℕ, 0 < n → Function.Bijective ((rawKStageHomotopyFunctor 0 n).map f)) ∧
      Function.Injective ((rawKStageHomotopyFunctor 0 0).map f)) := by
  have hb (n : ℕ) :
      Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) (n : ℤ)) ↔
        Function.Bijective ((rawKStageHomotopyFunctor 0 n).map f) := by
    have hd : OmegaSpectrum.degree (n : ℤ) 0 = n := by
      unfold OmegaSpectrum.degree
      omega
    exact hd ▸ kSpectrumMap_bijective_iff_rawStage f (n : ℤ) 0 (by omega)
  have hi : Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0) ↔
      Function.Injective ((rawKStageHomotopyFunctor 0 0).map f) := by
    have hd : OmegaSpectrum.degree 0 0 = 0 := rfl
    exact hd ▸ kSpectrumMap_injective_iff_rawStage f 0 0 (by omega)
  constructor
  · rintro ⟨h, h0⟩
    exact ⟨fun n hn => (hb n).mp (h n (by omega)), hi.mp h0⟩
  · rintro ⟨h, h0⟩
    refine ⟨?_, hi.mpr h0⟩
    intro j hj
    have hjn : (j.toNat : ℤ) = j := Int.toNat_of_nonneg (by omega)
    rw [← hjn]
    exact (hb j.toNat).mpr (h j.toNat (by omega))

end SerrePositivity.KST.SConstruction.Cofinality
