module
public import SerrePositivity.KST.SConstruction.KOmegaSpectrum
public import SerrePositivity.KST.Spectra.SpectrumHomotopyGroups

/-! # BF K スペクトルの負次数消滅と零段表示
概要：元の K の BF 模型は負の全整数次数で自明であり、零次数を元の K 空間で計算できる。
方針：負次数を正の段の零次数で計算し、正の全段の連結性を使う。
規約：L9 の実際の整数次数群を使う。使われ方：連結 K と三角圏 K₀ の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra

/-- 元の BF K スペクトルの全負次数のホモトピー群は一点。 -/
lemma kOmegaSpectrum_negative_subsingleton (X : StableModel.{u}) (j : ℤ) (hj : j < 0) :
    Subsingleton (OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) j) := by
  cases j with
  | ofNat n =>
    have hn : (0 : ℤ) ≤ Int.ofNat n := Int.natCast_nonneg n
    omega
  | negSucc n =>
    have hd : OmegaSpectrum.degree (Int.negSucc n) (n + 1) = 0 := by
      dsimp [OmegaSpectrum.degree]
      omega
    let z : OmegaSpectrum.levelHomotopy (kOmegaSpectrum X) (n + 1) 0 ≃
        SSet.π₀ (((kOmegaSpectrum X).level (n + 1)).space).right :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero
    have : Subsingleton (OmegaSpectrum.levelHomotopy (kOmegaSpectrum X) (n + 1) 0) :=
      z.injective.subsingleton
    have e : OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) (Int.negSucc n) ≃
        OmegaSpectrum.levelHomotopy (kOmegaSpectrum X) (n + 1) 0 := by
      simpa only [hd] using
        (OmegaSpectrum.homotopyGroupEquivAt
          (kOmegaSpectrum X) (Int.negSucc n) (n + 1) (by omega)).toEquiv
    exact e.injective.subsingleton

/-- 負次数の実際の整数ホモトピー群の任意の要素は単位。 -/
lemma kOmegaSpectrum_negative_eq_one (X : StableModel.{u}) (j : ℤ) (hj : j < 0)
    (a : OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) j) : a = 1 := by
  have := kOmegaSpectrum_negative_subsingleton X j hj
  exact Subsingleton.elim _ _

/-- BF K スペクトルの零次数群は元の境界商 K 空間の零次数群と同型。 -/
def kOmegaSpectrum_zeroGroupEquiv (X : StableModel.{u}) :
    OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0 ≃*
      OmegaSpectrum.levelHomotopy (kOmegaSpectrum X) 0 0 := by
  exact OmegaSpectrum.homotopyGroupEquivAt (kOmegaSpectrum X) 0 0 (by omega)

/-- BF K スペクトルの零次数は元の境界商 K 空間の連結成分で計算できる。 -/
def kOmegaSpectrum_zeroEquivPiZero (X : StableModel.{u}) :
    OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0 ≃
      SSet.π₀ (boundaryKSpaceFunctor.obj X).right :=
  (kOmegaSpectrum_zeroGroupEquiv X).toEquiv.trans _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero

end SerrePositivity.KST.SConstruction
