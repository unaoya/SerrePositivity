module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.TimeMinimumParameters

/-!
概要：錐の正方形の下辺から対角へ、両端固定で移すパラメータを構成する。
方針：横時刻を固定し、縦時刻を横時刻と変形時刻の最小値にする。
規約：全図式・全 Hom のパラメータを保持する。
使われ方：native な Hom 比較と三角形の長辺のホモトピー。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 元の時刻を正方形の両方向へ同時に入力する。 -/
def coneDiagonalParameters (K T : SSet.{u}) :
    (K ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ (K ⊗ (Δ[1] : SSet.{u})) ⊗ (T ⊗ (Δ[1] : SSet.{u})) where
  app _ := ↾fun a ↦ (a.1, (a.2, a.1.2))
  naturality {_ _} _ := rfl

/-- 下辺から同じ対角へ移す、全パラメータの最小値変形。 -/
def coneDiagonalDeformationParameters (K T : SSet.{u}) :
    ((K ⊗ (Δ[1] : SSet.{u})) ⊗ T) ⊗ (Δ[1] : SSet.{u}) ⟶
      (K ⊗ (Δ[1] : SSet.{u})) ⊗ (T ⊗ (Δ[1] : SSet.{u})) :=
  lift (fst ((K ⊗ Δ[1]) ⊗ T) Δ[1] ≫ fst (K ⊗ Δ[1]) T)
    (lift (fst ((K ⊗ Δ[1]) ⊗ T) Δ[1] ≫ snd (K ⊗ Δ[1]) T)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.timeMinimumAlong (fst (K ⊗ Δ[1]) T ≫ snd K Δ[1])))

/-- 変形の始点は元の正方形の下辺。 -/
lemma coneDiagonalDeformationParameters_zero (K T : SSet.{u}) :
    SSet.ι₀ ≫ coneDiagonalDeformationParameters K T =
      ((K ⊗ (Δ[1] : SSet.{u})) ◁ SSet.ι₀) := by
  rw [coneDiagonalDeformationParameters, comp_lift, comp_lift, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.timeMinimumAlong_zero]
  rfl

/-- 変形の終点は元の正方形の同じ対角。 -/
lemma coneDiagonalDeformationParameters_one (K T : SSet.{u}) :
    SSet.ι₁ ≫ coneDiagonalDeformationParameters K T = coneDiagonalParameters K T := by
  rw [coneDiagonalDeformationParameters, comp_lift, comp_lift, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.timeMinimumAlong_one]
  rfl

/-- 横の始点では縦時刻も全時間で零に固定される。 -/
lemma coneDiagonalDeformationParameters_left (K T : SSet.{u}) :
    ((SSet.ι₀ (X := K) ▷ T) ▷ (Δ[1] : SSet.{u})) ≫ coneDiagonalDeformationParameters K T =
      (fst (K ⊗ T) (Δ[1] : SSet.{u}) ≫ (SSet.ι₀ (X := K) ▷ T)) ≫
        ((K ⊗ (Δ[1] : SSet.{u})) ◁ SSet.ι₀) := by
  rw [coneDiagonalDeformationParameters, comp_lift, comp_lift, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.timeMinimumAlong_precomp]
  have h : (SSet.ι₀ (X := K) ▷ T) ≫ (fst (K ⊗ Δ[1]) T ≫ snd K Δ[1]) =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := rfl
  rw [h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.timeMinimumAlong_const_zero]
  rfl

/-- 横の終点では縦時刻だけが動き、右辺を通る。 -/
lemma coneDiagonalDeformationParameters_right (K T : SSet.{u}) :
    ((SSet.ι₁ (X := K) ▷ T) ▷ (Δ[1] : SSet.{u})) ≫ coneDiagonalDeformationParameters K T =
      (α_ K T (Δ[1] : SSet.{u})).hom ≫ (SSet.ι₁ ▷ (T ⊗ (Δ[1] : SSet.{u}))) := by
  rw [coneDiagonalDeformationParameters, comp_lift, comp_lift, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.timeMinimumAlong_precomp]
  have h : (SSet.ι₁ (X := K) ▷ T) ≫ (fst (K ⊗ Δ[1]) T ≫ snd K Δ[1]) =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := rfl
  rw [h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.timeMinimumAlong_const_one]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
