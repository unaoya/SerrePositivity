module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StandardHornFaceEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionFaceProjection

/-!
# 正の欠落面のホーンの射影の Kan 標的の同値性

概要：i ≠ 0 なら台によるホーンの旗の模型から標準ホーンへの最大元の射影は Kan 標的で同値。
方針：零頂点を除く面の射影と両側の面の包含の同値性を可換正方形で接続する。
規約：左 Kan 拡張との同定と i = 0 の場合はここでは主張しない。
使われ方：HA 1.3.1.17、Kerodon Proposition 4.6.7.23（Tag 01LW） の相対的な射影の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：ホーンの旗の部分複体の最大元の列は同じ標準ホーンに属する。
方針：旗の台の欠落頂点は全ての段の最大元の列でも欠けることを使う。
規約：ホーンの添字 i は任意。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） のホーンの旗の模型からの射影。 -/
def resolutionHornProjection {n : ℕ} (i : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHorn.{u} i).toSSet ⟶ (SSet.horn n i).toSSet :=
  SSet.Subcomplex.lift ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHorn i).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n) (by
    intro d σ hσ
    obtain ⟨⟨d⟩⟩ := d
    obtain ⟨G, rfl⟩ := hσ
    obtain ⟨j, hji, hj⟩ := G.property
    apply (SSet.mem_horn_iff_notMem_range _ i).mpr
    refine ⟨j, hji, ?_⟩
    rintro ⟨r, hr⟩
    change G.val.down.maxAt r = j at hr
    exact hj (hr ▸ G.val.down.sets_subset_support r (G.val.down.maxAt_mem r)))

/-- 概要：ホーンの射影は包含後に全体の解像の最大元の射影と一致する。
方針：部分複体への持ち上げの可換式を使う。
規約：任意のホーンの添字での射の等式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の面の射影との正方形の検証。 -/
lemma resolutionHornProjection_ι {n : ℕ} (i : Fin (n + 1)) :
    resolutionHornProjection.{u} i ≫ (SSet.horn n i).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHorn i).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n := rfl

/-- 概要：零頂点を除く面の射影とホーンの射影は両側の包含で可換する。
方針：標準ホーンの包含を後合成し、全体の最大元の射影の同じ制限を比較する。
規約：i ≠ 0 のときの実際の単体集合の射の等式。
使われ方：Kerodon Proposition 4.6.7.23（Tag 01LW） の面を介したホーンの比較。 -/
lemma resolutionHornProjection_positiveFace_square {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0) :
    SSet.Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace_le_horn.{u} i hi) ≫
        resolutionHornProjection i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceProjection (Finset.univ.erase 0) ≫
        SSet.Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.standardPositiveFace_le_horn i hi) := by
  apply (cancel_mono (SSet.horn n i).ι).1
  calc
    _ = SSet.Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace_le_horn i hi) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHorn i).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n := by
      rw [Category.assoc, resolutionHornProjection_ι]
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace n).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n := by
      rw [← Category.assoc, SSet.Subcomplex.homOfLE_ι]
    _ = _ := by
      rw [Category.assoc, SSet.Subcomplex.homOfLE_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceProjection_ι]
      rfl

/-- 概要：正の欠落面のホーンの射影は任意の Kan 標的への前合成で同値になる。
方針：面の射影と標準側の包含の同値性を合成し、解像側の包含を消去する。
規約：台で定義したホーンの模型に対する実際の写像空間のホモトピー同値性。
使われ方：HA 1.3.1.17 の解像の比較の相対的なホーンの場合。 -/
lemma resolutionHornProjection_isKanPrecompositionEquivalence_of_ne_zero {n : ℕ}
    (i : Fin (n + 1)) (hi : i ≠ 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IsKanPrecompositionEquivalence (resolutionHornProjection.{u} i) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isKanPrecompositionEquivalence_cancel_left
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionPositiveFace_inclusion_isKanPrecompositionEquivalence i hi)
  rw [resolutionHornProjection_positiveFace_square i hi]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isKanPrecompositionEquivalence_comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isKanPrecompositionEquivalence_of_precompositionEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionFaceProjection_isPrecompositionEquivalence (Finset.univ.erase 0)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.standardPositiveFace_inclusion_isKanPrecompositionEquivalence i hi)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
