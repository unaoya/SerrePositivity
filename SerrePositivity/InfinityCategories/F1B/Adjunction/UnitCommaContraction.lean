module

public import SerrePositivity.InfinityCategories.F1B.KanComplex.HomotopyMaximum
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaHomotopySquare
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaCounit

/-!
概要：comma の各矢印を標的の恒等矢印へ標的を固定して変形する。
方針：普遍な矢印の時間を最大値の正方形で縮め、comma の普遍性へ渡す。
規約：全ての単体集合と関手を任意とする。
使われ方：元の添字の包含から oriented comma の恒等射への比較の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：矢印の始域を矢印に沿って動かし標的を固定した comma の族。
方針：二つの時間の最大値で普遍な矢印を評価して comma に持ち上げる。
規約：最初の時間が変形の時間。
使われ方：comma の恒等矢印への変形の射。 -/
def unitCommaContractionFamily {X Y : SSet.{u}} (G : Y ⟶ X) :
    unitComma G ⊗ (Δ[1] : SSet.{u}) ⟶ unitComma G :=
  unitCommaLift G (unitCommaHomotopy (𝟙 (unitComma G))).h
    (fst (unitComma G) Δ[1] ≫ unitCommaTarget G)
    (kanHomotopyMaximum (unitCommaHomotopy (𝟙 (unitComma G))))

/-- 概要：変形の始点は comma の恒等射。
方針：矢印の族と標的への射影を比較する。
規約：両端の射は厳密に等しい。
使われ方：comma の変形の零境界。 -/
lemma unitCommaContractionFamily_zero {X Y : SSet.{u}} (G : Y ⟶ X) :
    (SSet.ι₀ : unitComma G ⟶ unitComma G ⊗ (Δ[1] : SSet.{u})) ≫
      unitCommaContractionFamily G = 𝟙 _ := by
  apply unitComma_hom_ext
  · apply (cancel_epi (β_ (unitComma G) (Δ[1] : SSet.{u})).hom).1
    change (unitCommaHomotopy (_ ≫ _)).h = (unitCommaHomotopy _).h
    rw [unitCommaHomotopy_precomp]
    unfold unitCommaContractionFamily
    rw [unitCommaHomotopy_lift_h, kanHomotopyMaximum_first_zero_h]
  · rw [Category.assoc, Category.id_comp]
    unfold unitCommaContractionFamily
    rw [unitCommaLift_target, ← Category.assoc, SSet.ι₀_fst, Category.id_comp]

/-- 概要：変形の終点は標的の恒等矢印の族。
方針：矢印は標的に定値、標的への射影は元のままであることを使う。
規約：標的射影の後に恒等矢印の包含を続ける。
使われ方：comma の変形の一境界。 -/
lemma unitCommaContractionFamily_one {X Y : SSet.{u}} (G : Y ⟶ X) :
    (SSet.ι₁ : unitComma G ⟶ unitComma G ⊗ (Δ[1] : SSet.{u})) ≫
      unitCommaContractionFamily G = unitCommaTarget G ≫ unitCommaIdentityFamily G := by
  apply unitComma_hom_ext
  · apply (cancel_epi (β_ (unitComma G) (Δ[1] : SSet.{u})).hom).1
    change (unitCommaHomotopy (_ ≫ _)).h = (unitCommaHomotopy (_ ≫ _)).h
    rw [unitCommaHomotopy_precomp, unitCommaHomotopy_precomp]
    unfold unitCommaContractionFamily unitCommaIdentityFamily
    rw [unitCommaHomotopy_lift_h, unitCommaHomotopy_lift_h,
      kanHomotopyMaximum_first_one_h]
    rfl
  · rw [Category.assoc, Category.assoc, unitCommaIdentityFamily_target, Category.comp_id]
    unfold unitCommaContractionFamily
    rw [unitCommaLift_target, ← Category.assoc, SSet.ι₁_fst, Category.id_comp]

/-- 概要：comma の恒等射から標的の恒等矢印への指定ホモトピー。
方針：最大値による族に二つの境界の計算を付ける。
規約：quasicategory 性を要求しない。
使われ方：反転して oriented comma 内の比較を得る。 -/
def unitCommaContraction {X Y : SSet.{u}} (G : Y ⟶ X) :
    SSet.Homotopy (𝟙 (unitComma G)) (unitCommaTarget G ≫ unitCommaIdentityFamily G) where
  h := unitCommaContractionFamily G
  h₀ := unitCommaContractionFamily_zero G
  h₁ := unitCommaContractionFamily_one G
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：comma 内の変形は標的を固定する。
方針：comma の持ち上げの標的射影の公式。
規約：時間に定値な標的の族。
使われ方：反転した比較で元の添字を厳密に固定する。 -/
lemma unitCommaContraction_target {X Y : SSet.{u}} (G : Y ⟶ X) :
    (unitCommaContraction G).h ≫ unitCommaTarget G =
      fst (unitComma G) Δ[1] ≫ unitCommaTarget G := by
  change unitCommaContractionFamily G ≫ unitCommaTarget G = _
  unfold unitCommaContractionFamily
  exact unitCommaLift_target G (unitCommaHomotopy (𝟙 (unitComma G))).h
    (fst (unitComma G) Δ[1] ≫ unitCommaTarget G)
    (kanHomotopyMaximum (unitCommaHomotopy (𝟙 (unitComma G))))

/-- 概要：comma 内の変形の始域射影は普遍な矢印の族。
方針：comma の持ち上げの始域射影の公式。
規約：矢印の時間は変形の時間になる。
使われ方：oriented comma の比較が標準の指定変換を表すことの確認。 -/
lemma unitCommaContraction_source {X Y : SSet.{u}} (G : Y ⟶ X) :
    (unitCommaContraction G).h ≫ unitCommaSource G =
      (unitCommaHomotopy (𝟙 (unitComma G))).h := by
  change unitCommaContractionFamily G ≫ unitCommaSource G = _
  unfold unitCommaContractionFamily
  exact unitCommaLift_source G (unitCommaHomotopy (𝟙 (unitComma G))).h
    (fst (unitComma G) Δ[1] ≫ unitCommaTarget G)
    (kanHomotopyMaximum (unitCommaHomotopy (𝟙 (unitComma G))))

end SerrePositivity.InfinityCategories.F1B
