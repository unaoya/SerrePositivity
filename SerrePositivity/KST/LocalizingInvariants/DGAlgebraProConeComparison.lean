module

public import SerrePositivity.KST.LocalizingInvariants.CochainProCone
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantProConnectivity
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantEventualProConnectivity

/-!
概要：元の dg 代数射の cone の pro 消滅を、元の射と不変量値の pro 判定へ接続する。
方針：実 cone の長完全列の次数を H⁻ʲ に合わせ、β6 の連結なレベル表示を適用する。
規約：Tor と cone の同定は別途検証し、一般 pro ∞ 同値や切除とは同一視しない。
使われ方：K-8 e の Tor 比較の欠損から実比較射へ戻る抽象部分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R]
  {A B : Tower (Mon (Complex R))} (f : LevelHom A B)

/-- 元の射の実 mapping cone を、元の全遷移のまま取る。 -/
def comparisonConeTower : Tower (Complex R) :=
  CochainProCone.tower R (f.map (Mon.forget (Complex R)))

/-- 同じ cone の H⁻ʲ の塔。次数のずれを省略しない。 -/
def comparisonConeGroups (j : ℤ) : Tower CommGrpCat.{u} :=
  (comparisonConeTower R f).map (complexGroups R j)

/-- 全整数次数の cone pro 零性は、元の代数射の次数別 pro 同型と同値。 -/
lemma comparisonCone_proZero_iff_piProEquivalence :
    (∀ j : ℤ, IsProZero (comparisonConeGroups R f j)) ↔ IsPiProEquivalence R f := by
  constructor
  · intro h j
    exact CochainProCone.map_isProIso R (f.map (Mon.forget (Complex R))) (-j)
      (by simpa only [comparisonConeGroups, comparisonConeTower, complexGroups,
        CochainProCone.homologyGroups, show -(j + 1) = -j - 1 by omega] using h (j + 1)) (h j)
  · intro h j
    exact CochainProCone.cone_isProZero R (f.map (Mon.forget (Complex R))) (-j)
      (h j) (by
        have hh := h (j - 1)
        change IsProIso ((f.map (Mon.forget (Complex R))).map
          (CochainProCone.homologyGroups R (-(j - 1)))) at hh
        rw [show -(j - 1) = -j + 1 by omega] at hh
        exact hh)

/-- 指定次数までの cone pro 零性と、元の比較射の pro 連結度判定を照合する。 -/
lemma comparisonCone_proZero_iff_piProConnected (n : ℤ) :
    (∀ j : ℤ, j ≤ n → IsProZero (comparisonConeGroups R f j)) ↔
      IsPiProConnected R f n := by
  constructor
  · intro h
    constructor
    · intro j hj
      exact CochainProCone.map_eventuallyKernelTrivial R
        (f.map (Mon.forget (Complex R))) (-j)
        (by simpa only [comparisonConeGroups, comparisonConeTower, complexGroups,
        CochainProCone.homologyGroups, show -(j + 1) = -j - 1 by omega] using h (j + 1) (by omega))
    · intro j hj
      exact CochainProCone.map_eventuallyImageSurjective R
        (f.map (Mon.forget (Complex R))) (-j) (h j hj)
  · intro h j hj
    exact CochainProCone.cone_isProZero_of_kernel_image R
      (f.map (Mon.forget (Complex R))) (-j) (h.2 j hj)
      (by
        have hh := h.1 (j - 1) (by omega)
        change ProGroup.IsEventuallyKernelTrivial ((f.map (Mon.forget (Complex R))).map
          (CochainProCone.homologyGroups R (-(j - 1)))) at hh
        rw [show -(j - 1) = -j + 1 by omega] at hh
        exact hh)

variable {X Y : Tower (NonpositiveAlgebra R)} (g : LevelHom X Y)
  (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}) {k : ℤ} (hΦ : IsKConnective R Φ k)
include hΦ

/-- 実 cone の次数範囲付き pro 消滅から、元の不変量値の連結度を得る。 -/
lemma IsKConnective.invariantLevelMap_piProConnected_of_comparisonCone
    (n : ℤ) (hn : 1 ≤ n)
    (hc : ∀ j : ℤ, j ≤ n →
      IsProZero (comparisonConeGroups R (g.map (nonpositiveInclusion R)) j)) :
    ProSpectrum.IsPiProConnected
      (invariantLevelMap R Φ (g.map (nonpositiveInclusion R))) (n + k) :=
  hΦ.invariantLevelMap_piProConnected R g Φ n hn
    ((comparisonCone_proZero_iff_piProConnected R _ n).1 hc)

/-- 実 cone の全次数 pro 消滅から、元の不変量値の π-pro 同値を得る。 -/
lemma IsKConnective.invariantLevelMap_piProEquivalence_of_comparisonCone
    (hc : ∀ j : ℤ,
      IsProZero (comparisonConeGroups R (g.map (nonpositiveInclusion R)) j)) :
    ProSpectrum.IsPiProEquivalence
      (invariantLevelMap R Φ (g.map (nonpositiveInclusion R))) :=
  hΦ.invariantLevelMap_piProEquivalence_of_piProEquivalence R g Φ
    ((comparisonCone_proZero_iff_piProEquivalence R _).1 hc)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
