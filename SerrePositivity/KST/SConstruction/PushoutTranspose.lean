module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pasting

/-! # 押し出し正方形の転置
概要：正方形の二座標を交換しても押し出し性は変わらない。
方針：span の二辺を交換する同型を余錐の join 表示に適用する。
規約：値域は quasicategory。使われ方：HTT Lemma 4.4.2.1 の縦方向への適用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：span ホーンの二つの終点を交換する。
方針：共通の始点を固定して二辺を逆の順序で貼る。
規約：辺の向きは変えない。使われ方：正方形の転置。 -/
def spanTranspose : (horn 2 0 : SSet.{u}) ⟶ (horn 2 0 : SSet.{u}) :=
  horn₂₀.isPushout.desc horn₂₀.ι₀₂ horn₂₀.ι₀₁ horn₂₀.isPushout.w.symm

/-- 概要：span の転置は第一辺を第二辺へ送る。
方針：pushout の第一包含の計算。規約：厳密等号。使われ方：余錐形状の照合。 -/
lemma spanTranspose_left : horn₂₀.ι₀₁ ≫ spanTranspose.{u} = horn₂₀.ι₀₂ :=
  horn₂₀.isPushout.inl_desc _ _ _

/-- 概要：span の転置は第二辺を第一辺へ送る。
方針：pushout の第二包含の計算。規約：厳密等号。使われ方：余錐形状の照合。 -/
lemma spanTranspose_right : horn₂₀.ι₀₂ ≫ spanTranspose.{u} = horn₂₀.ι₀₁ :=
  horn₂₀.isPushout.inr_desc _ _ _

/-- 概要：span の転置を二回行うと恒等射。
方針：二辺に制限して pushout の一意性を使う。
規約：厳密等号。使われ方：転置の同型構造。 -/
lemma spanTranspose_comp_self : spanTranspose.{u} ≫ spanTranspose = 𝟙 _ := by
  apply horn₂₀.isPushout.hom_ext <;>
    simp only [← Category.assoc, spanTranspose_left, spanTranspose_right, Category.comp_id]

/-- 概要：span の転置は同型。
方針：同じ転置を逆射に取る。規約：形状の同型。使われ方：余極限の制限。 -/
def spanTransposeIso : (horn 2 0 : SSet.{u}) ≅ (horn 2 0 : SSet.{u}) where
  hom := spanTranspose
  inv := spanTranspose
  hom_inv_id := spanTranspose_comp_self
  inv_hom_id := spanTranspose_comp_self

/-- 概要：span の転置は同型射。
方針：明示した同型の射であることを使う。
規約：型クラス用。使われ方：right anodyne な制限。 -/
instance spanTranspose_isIso : IsIso spanTranspose.{u} := spanTransposeIso.isIso_hom

/-- 概要：span の転置は余錐正方形の二座標の交換に対応する。
方針：余錐の二三角形への制限を計算する。
規約：余錐の頂点は固定。使われ方：転置した押し出しの余極限判定。 -/
lemma spanTranspose_square :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap spanTranspose.{u} (𝟙 (Δ[0] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ (β_ (Δ[1] : SSet.{u}) Δ[1]).hom := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCocone_isPushout.hom_ext
  · have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap spanTranspose (𝟙 (Δ[0] : SSet.{u})) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight := by
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight, Category.assoc,
        ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, spanTranspose_left, Category.id_comp]
    rw [← Category.assoc, he, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_right,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_left]
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  · have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap spanTranspose (𝟙 (Δ[0] : SSet.{u})) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft := by
      simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight, Category.assoc,
        ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, spanTranspose_right, Category.id_comp]
    rw [← Category.assoc, he, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_left,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_right]
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide

/-- 概要：押し出し正方形を転置しても押し出し。
方針：span の同型による余錐の制限で余極限性を移す。
規約：C は quasicategory。使われ方：押し出しの縦方向の相殺。 -/
lemma IsPushoutSquare.transpose {C : SSet.{u}} [Quasicategory C]
    {F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C} (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ F) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone.restrict_of_rightAnodyne hF spanTranspose
    (MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions spanTranspose)
  apply (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq _ _ ?_).1 h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap spanTranspose (𝟙 (Δ[0] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ F) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ F)
  rw [← Category.assoc, spanTranspose_square, Category.assoc]

end SerrePositivity.KST.SConstruction
