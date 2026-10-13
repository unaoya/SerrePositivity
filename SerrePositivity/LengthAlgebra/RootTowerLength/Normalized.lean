module

public import SerrePositivity.LengthAlgebra.RootTowerLength.AdditivityFinitelyGenerated
public import SerrePositivity.PerfectComplex.SupProperty

/-! # 証明した加法性から組み立てる根の塔の正規化長さ

Noether 局所基底と極大イデアル内の座標について、三段階の数値定義から
加法性・有限生成一致を証明し、具体的な NormalizedLength を構成する。
旧 Paper 層の広い型の長さ構成・C2 引用には依存しない。
-/

@[expose] public section
universe u
namespace SerrePositivity.RootTowerLength
open Section2 IsLocalRing
open scoped ENNReal

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A)

/-- 有限段の長さと近似から証明した法則を持つ、具体的な根の塔の正規化長さ。
基底と座標の仮定を明示し、加法性を文献の引用で埋めない。 -/
noncomputable def normalizedLength :
    NormalizedLength (Tower A t p) (towerMaxIdeal A t p) where
  len M _ _ := towerLengthFun A t p M
  len_eq_zero_of_subsingleton M _ _ _ := towerLengthFun_eq_zero_of_subsingleton M
  len_congr _ _ _ _ _ _ e := towerLengthFun_congr e
  len_add_of_exact _ _ _ _ _ _ _ _ _ f g hf hg hfg hM :=
    towerLengthFun_add_of_exact_of_noetherian A t p ht f g hf hg hfg hM

/-- 新しい正規化長さの値は既存の三段階の数値関数と定義上同じ。 -/
@[simp] theorem normalizedLength_len (M : Type u) [AddCommGroup M]
    [Module (Tower A t p) M] :
    (normalizedLength A t p ht).len M = towerLengthFun A t p M := rfl

/-- 証明した有限生成一致から、正規化長さの上限の性質を供給する。
長さの構造そのものも、その性質の証明も未証明の C2 に依存しない。 -/
theorem normalizedLength_hasSup : (normalizedLength A t p ht).HasSup := by
  intro M _ _ hM
  rw [normalizedLength_len, towerLengthFun]
  refine le_antisymm (iSup₂_le fun N hN ↦ le_iSup₂_of_le N hN (le_of_eq ?_))
    (iSup₂_le fun N hN ↦ le_iSup₂_of_le N hN (le_of_eq ?_))
  · have : Module.Finite (Tower A t p) N := Module.Finite.iff_fg.mpr hN
    rw [normalizedLength_len, towerLengthFun_eq_fgLength_of_noetherian A t p ht N]
  · have : Module.Finite (Tower A t p) N := Module.Finite.iff_fg.mpr hN
    rw [normalizedLength_len, towerLengthFun_eq_fgLength_of_noetherian A t p ht N]

end SerrePositivity.RootTowerLength
