module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraProTorCriterion

/-!
概要：元の ⊙ 比較の dg 塔と、Tor 欠損への実ホモロジー比較の供給界面を固定する。
方針：二つの未供給界面を分け、同じ元の射と全遷移を抽象 pro 判定へ渡す。
規約：構造体の実在は主張しない。欠損の添字は cone の H⁻ʲ で、零次数も省略しない。
使われ方：K-S•-S4 の供給後に、追加の値比較を仮定せず K-8 e を接続する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R]

/-- 所有レーンが供給する元の ⊙→B′ の非正次数 dg 代数の塔。
元の比較射の型と遷移を保持し、その存在はこの宣言からは得ない。 -/
structure ProComparisonTowerInput where
  source : Tower (NonpositiveAlgebra R)
  target : Tower (NonpositiveAlgebra R)
  comparison : LevelHom source target

variable {R}

/-- 元の cone の H⁻ʲ と、同じ次数に配置した Tor 欠損の全遷移に自然な比較。
欠損模型の供給者が Tor の次数ずれと零次数の核・余核を照合する。
各対象の群同型だけでは足りず、同じ塔のレベル射とその全成分の可逆性を要求する。 -/
structure ProComparisonConeHomologyInput (c : ProComparisonTowerInput R) where
  defect : ℤ → Tower CommGrpCat.{u}
  identification (j : ℤ) : LevelHom (defect j)
    (comparisonConeGroups R (c.comparison.map (nonpositiveInclusion R)) j)
  identification_isIso (j : ℤ) (i : ℕ) : IsIso ((identification j).app i)

namespace ProComparisonConeHomologyInput
variable {c : ProComparisonTowerInput R} (d : ProComparisonConeHomologyInput c)

/-- 実同定を使うと、Tor 欠損の pro 消滅は元の cone の pro 消滅へ移る。 -/
lemma cone_proZero (h : ∀ j : ℤ, IsProZero (d.defect j)) (j : ℤ) :
    IsProZero (comparisonConeGroups R (c.comparison.map (nonpositiveInclusion R)) j) := by
  have : ∀ i, IsIso ((d.identification j).app i) := d.identification_isIso j
  exact IsProZero.of_levelwiseIso (d.identification j) (h j)

/-- 欠損の pro 消滅から元の dg 比較射の全整数 π-pro 同値を得る。 -/
lemma comparison_piProEquivalence (h : ∀ j : ℤ, IsProZero (d.defect j)) :
    IsPiProEquivalence R (c.comparison.map (nonpositiveInclusion R)) :=
  (comparisonCone_proZero_iff_piProEquivalence R _).1 (d.cone_proZero h)

/-- 零次数も同じ元の射の pro 同型として回収し、別の比較を選ばない。 -/
lemma comparison_piZero_isProIso (h : ∀ j : ℤ, IsProZero (d.defect j)) :
    IsProIso ((c.comparison.map (nonpositiveInclusion R)).map (groups R 0)) :=
  d.comparison_piProEquivalence h 0

/-- 同じ元の dg 比較射を、β6 の実不変量値の π-pro 同値へ送る。
局所化・模型・関手的レベル表示の追加仮定は要求しない。 -/
lemma invariant_piProEquivalence
    (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}) {k : ℤ} (hΦ : IsKConnective R Φ k)
    (h : ∀ j : ℤ, IsProZero (d.defect j)) :
    ProSpectrum.IsPiProEquivalence
      (invariantLevelMap R Φ (c.comparison.map (nonpositiveInclusion R))) :=
  hΦ.invariantLevelMap_piProEquivalence_of_comparisonCone R c.comparison Φ (d.cone_proZero h)

/-- 指定次数までの実欠損の pro 消滅は、元の不変量値の指定連結度へ移る。 -/
lemma invariant_piProConnected
    (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}) {k : ℤ} (hΦ : IsKConnective R Φ k)
    (n : ℤ) (hn : 1 ≤ n)
    (h : ∀ j : ℤ, j ≤ n → IsProZero (d.defect j)) :
    ProSpectrum.IsPiProConnected
      (invariantLevelMap R Φ (c.comparison.map (nonpositiveInclusion R))) (n + k) := by
  apply hΦ.invariantLevelMap_piProConnected_of_comparisonCone R c.comparison Φ n hn
  intro j hj
  have : ∀ i, IsIso ((d.identification j).app i) := d.identification_isIso j
  exact IsProZero.of_levelwiseIso (d.identification j) (h j hj)

end ProComparisonConeHomologyInput
end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
