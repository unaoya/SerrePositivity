module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.PointSliceOppositeHomotopy
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftKanShapeCommaProjection
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftKanShapeCommaComparison

/-!
概要：局所 Kan 添字の反転同型は標準の指定変換を反転した指定変換へ移す。
方針：slice への射影を追跡し、coslice の変換のパラメータ自然性と点の反転を使う。
規約：quasicategory 性を使わない。
使われ方：元の局所添字の比較が標準の矢印を保持することの証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：局所添字の反転同型は slice への射影も正規化した反転へ移す。
方針：引き戻しの二射影と反転の pullback 保存同型を計算する。
規約：slice の元の標準頂点表示を保つ。
使われ方：標準の指定変換の反転の計算。 -/
lemma kanLeftKanShapeOpIso_slice {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (kanLeftKanShapeOpIso δ c).hom ≫
      pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm c)))
        (SSet.opFunctor.map δ) =
      SSet.opFunctor.map (pullback.snd δ (sliceOverProjection (SSet.yonedaEquiv.symm c))) ≫
        (cofinalPointSliceOverOpIso c).hom.left := by
  dsimp only [kanLeftKanShapeOpIso, cofinalSlicePullbackOpIso, Iso.trans_hom]
  simp only [Category.assoc, pullbackSymmetry_hom_comp_fst, asIso_hom, pullback.lift_snd]
  rw [← Category.assoc, PreservesPullback.iso_hom_snd]

/-- 概要：点の coslice の指定変換はパラメータの前合成と可換。
方針：左の円柱比較と coslice の展開の自然性。
規約：raw な円柱の射の厳密な等式。
使われ方：局所添字の反転同型による変換の制限。 -/
lemma kanPointCosliceHomotopy_precomp_h {A B X : SSet.{u}} (x : X _⦋0⦌)
    (f : A ⟶ sliceUnder (SSet.yonedaEquiv.symm x)) (i : B ⟶ A) :
    (i ▷ (Δ[1] : SSet.{u})) ≫ (kanPointCosliceHomotopy x f).h =
      (kanPointCosliceHomotopy x (i ≫ f)).h := by
  have hb : (i ▷ (Δ[1] : SSet.{u})) ≫ (β_ A (Δ[1] : SSet.{u})).hom =
      (β_ B (Δ[1] : SSet.{u})).hom ≫ ((Δ[1] : SSet.{u}) ◁ i) := rfl
  dsimp only [kanPointCosliceHomotopy]
  rw [← Category.assoc, hb, Category.assoc, ← Category.assoc ((Δ[1] : SSet.{u}) ◁ i),
    leftMappingSpacePrism_naturality, Category.assoc, ← sliceUnderUncurry_precomp]

/-- 概要：局所 Kan 添字の反転同型による標準変換の制限は元の標準変換の反転。
方針：coslice の変換の自然性、slice 射影の反転、点の変換の反転を合成する。
規約：端点の図式の等式の移送を避け、raw な円柱の射を比較する。
使われ方：反転による局所比較と元の標準余錐からの比較を照合する。 -/
lemma kanLeftKanShapeOpIso_homotopy {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    ((kanLeftKanShapeOpIso δ c).hom ▷ (Δ[1] : SSet.{u})) ≫
      (kanRightKanShapeHomotopy (SSet.opFunctor.map δ) (SSet.opObjEquiv.symm c)).h =
        (SerrePositivity.InfinityCategories.homotopyOpposite (kanLeftKanShapeHomotopy δ c)).h := by
  change ((kanLeftKanShapeOpIso δ c).hom ▷ (Δ[1] : SSet.{u})) ≫
    (kanPointCosliceHomotopy (SSet.opObjEquiv.symm c) _).h = _
  rw [kanPointCosliceHomotopy_precomp_h, kanLeftKanShapeOpIso_slice,
    kanPointSliceOverOpIso_homotopy]
  rfl

end SerrePositivity.InfinityCategories.F1B
