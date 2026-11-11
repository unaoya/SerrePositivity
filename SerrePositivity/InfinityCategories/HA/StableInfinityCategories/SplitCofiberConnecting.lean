module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SplitCofiberRectangle
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberTriangle

/-! # 分裂する cofiber 列の接続射

概要：第二射が分裂全射である cofiber 列の接続射は零である。
方針：既存の合成零を全射で消去する。
規約：加法構造を仮定しない。使われ方：和の包含の三角形と双積の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：第二射が全射である cofiber 列の接続射は零となる。
方針：第二射との合成零を全射性で消去する。
規約：安定な quasicategory で、分裂性より弱い全射性だけを使う。
使われ方：和の射影の切断から接続射の消滅を得る。 -/
lemma cofiberConnecting_eq_zero_of_epi {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) [Epi t.hoShortComplex.g] :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht = 0 := by
  apply (cancel_epi t.hoShortComplex.g).1
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting_comp_eq_zero, comp_zero]

/-- 概要：第二射が全射である cofiber 三角形の第三射は零となる。
方針：接続射の消滅を整数シフトへの比較同型と合成する。
規約：前加法構造は不要。使われ方：分裂三角形の判定。 -/
lemma cofiberTriangle_mor₃_eq_zero_of_epi {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) [Epi t.hoShortComplex.g] :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht).mor₃ = 0 := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht ≫ _ = 0
  rw [cofiberConnecting_eq_zero_of_epi, zero_comp]

/-- 概要：零始点の押し出しの第一包含は接続射が零の分裂 cofiber/fiber 列を持つ。
方針：指定した包含の列を構成し、第二射の切断から接続射を消去する。
規約：包含と三対象を厳密に保つ。使われ方：二項和と積の比較。 -/
lemma exists_splitCofiber_of_zeroSourcePushout {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (L : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare L)
    (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex L 0 0)) :
    ∃ (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ L ∧
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0 = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex L 1 0 ∧
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 0 = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex L 1 1 ∧
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 1 = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex L 0 1 ∧
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t ∧ IsSplitEpi (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight t.square) ∧ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht = 0 := by
  obtain ⟨t, hb, h₀, h₁, h₂, ht, hf, hs⟩ :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_cofiberSequence_of_zeroSourcePushout L hL hz
  let : IsSplitEpi t.hoShortComplex.g := hs
  exact ⟨t, ht, hb, h₀, h₁, h₂, hf, hs, cofiberConnecting_eq_zero_of_epi t ht⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
