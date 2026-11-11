module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.TimeMaximumParameters
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeSquareParameters

/-!
概要：余錐の正方形の対角と、その対角を上辺へ移すパラメータの変形。
方針：元の横時刻を保ち、縦時刻だけを二時刻の最大値に変える。
規約：図式と Hom のパラメータを全て保持する。
使われ方：両端固定の対角と余錐族の比較ホモトピー。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：同じ時刻を正方形の横縦へ同時に入力する。
方針：時刻を複製する。規約：元のパラメータを保持。使われ方：三角形の長辺。 -/
def coconeDiagonalParameters (K T : SSet.{u}) :
    (K ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ (K ⊗ (Δ[1] : SSet.{u})) ⊗ (T ⊗ (Δ[1] : SSet.{u})) where
  app _ := ↾fun a ↦ (a.1, (a.2, a.1.2))
  naturality {_ _} _ := rfl

/-- 概要：正方形の対角を上辺へ移す全パラメータの変形。
方針：縦時刻だけを元の横時刻と変形時刻の最大値に変える。
規約：横時刻は変えない。使われ方：対角の比較ホモトピーの評価射。 -/
def coconeDiagonalDeformationParameters (K T : SSet.{u}) :
    ((K ⊗ (Δ[1] : SSet.{u})) ⊗ T) ⊗ (Δ[1] : SSet.{u}) ⟶
      (K ⊗ (Δ[1] : SSet.{u})) ⊗ (T ⊗ (Δ[1] : SSet.{u})) :=
  lift (fst ((K ⊗ Δ[1]) ⊗ T) Δ[1] ≫ fst (K ⊗ Δ[1]) T)
    (lift (fst ((K ⊗ Δ[1]) ⊗ T) Δ[1] ≫ snd (K ⊗ Δ[1]) T)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.timeMaximumAlong (fst (K ⊗ Δ[1]) T ≫ snd K Δ[1])))

/-- 概要：変形の始点は元の対角。
方針：最大値の零端を計算する。規約：全単体。使われ方：比較の始点。 -/
lemma coconeDiagonalDeformationParameters_zero (K T : SSet.{u}) :
    SSet.ι₀ ≫ coconeDiagonalDeformationParameters K T = coconeDiagonalParameters K T := by
  rw [coconeDiagonalDeformationParameters, comp_lift, comp_lift, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.timeMaximumAlong_zero]
  rfl

/-- 概要：変形の終点は正方形の上辺への包含。
方針：最大値の一端を計算する。規約：全単体。使われ方：元の余錐族の変換への到達。 -/
lemma coconeDiagonalDeformationParameters_one (K T : SSet.{u}) :
    SSet.ι₁ ≫ coconeDiagonalDeformationParameters K T =
      ((K ⊗ (Δ[1] : SSet.{u})) ◁ SSet.ι₁) := by
  rw [coconeDiagonalDeformationParameters, comp_lift, comp_lift, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.timeMaximumAlong_one]
  rfl

/-- 概要：横の始点では縦時刻だけが動く。
方針：最大値の第一時刻零を計算する。規約：全時間。使われ方：固定図式の境界。 -/
lemma coconeDiagonalDeformationParameters_left (K T : SSet.{u}) :
    ((SSet.ι₀ (X := K) ▷ T) ▷ (Δ[1] : SSet.{u})) ≫
      coconeDiagonalDeformationParameters K T =
        (α_ K T (Δ[1] : SSet.{u})).hom ≫ (SSet.ι₀ ▷ (T ⊗ (Δ[1] : SSet.{u}))) := by
  rw [coconeDiagonalDeformationParameters, comp_lift, comp_lift, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.timeMaximumAlong_precomp]
  have h : (SSet.ι₀ (X := K) ▷ T) ≫ (fst (K ⊗ Δ[1]) T ≫ snd K Δ[1]) =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := rfl
  rw [h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.timeMaximumAlong_const_zero]
  rfl

/-- 概要：横の終点では縦時刻も一に固定される。
方針：最大値の第一時刻一を計算する。規約：全時間。使われ方：固定終点の境界。 -/
lemma coconeDiagonalDeformationParameters_right (K T : SSet.{u}) :
    ((SSet.ι₁ (X := K) ▷ T) ▷ (Δ[1] : SSet.{u})) ≫
      coconeDiagonalDeformationParameters K T =
        (fst (K ⊗ T) (Δ[1] : SSet.{u}) ≫ (SSet.ι₁ (X := K) ▷ T)) ≫
          ((K ⊗ (Δ[1] : SSet.{u})) ◁ SSet.ι₁) := by
  rw [coconeDiagonalDeformationParameters, comp_lift, comp_lift, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.timeMaximumAlong_precomp]
  have h : (SSet.ι₁ (X := K) ▷ T) ≫ (fst (K ⊗ Δ[1]) T ≫ snd K Δ[1]) =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := rfl
  rw [h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.timeMaximumAlong_const_one]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
