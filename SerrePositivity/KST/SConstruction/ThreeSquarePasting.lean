module
public import SerrePositivity.KST.SConstruction.FamilyInterchangeSquares
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # 元の共有区間に沿って貼る三つの正方形
概要：三正方形を二つの元の共有区間に沿う pushout で貼り、各正方形を全体として回収する。
方針：最初の共有縦辺で二正方形を貼り、中央の共有横辺で第三の正方形を貼る。
規約：辺や正方形を置き換えず、全次数での実際の貼り合わせを使う。
使われ方：元の K 合成 prism と指定適合三角形を保つ貼り合わせ複体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 指定した座標に固定した正方形の縦辺。 -/
def pastingSquareVertical (b : Fin 2) : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  lift (SSet.const (stdSimplex.obj₀Equiv.symm b)) (𝟙 _)

/-- 指定した座標に固定した正方形の横辺。 -/
def pastingSquareHorizontal (b : Fin 2) : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  lift (𝟙 _) (SSet.const (stdSimplex.obj₀Equiv.symm b))

/-- 元の区間の二つの頂点。 -/
def pastingIntervalVertex (b : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1] :=
  SSet.const (stdSimplex.obj₀Equiv.symm b)

/-- 元の横辺の始点は、零番目の縦辺の指定頂点。 -/
lemma pastingSquareHorizontal_start (b : Fin 2) :
    pastingIntervalVertex 0 ≫ pastingSquareHorizontal.{u} b =
      pastingIntervalVertex b ≫ pastingSquareVertical 0 := by
  fin_cases b <;> rfl

/-- 元の縦辺の始点は、零番目の横辺の指定頂点。 -/
lemma pastingSquareVertical_start (b : Fin 2) :
    pastingIntervalVertex 0 ≫ pastingSquareVertical.{u} b =
      pastingIntervalVertex b ≫ pastingSquareHorizontal 0 := by
  fin_cases b <;> rfl

/-- 最初と中央の正方形の共有縦辺での貼り合わせ。 -/
def firstTwoSquarePasting : SSet.{u} :=
  pushout (pastingSquareVertical 0) (pastingSquareVertical 0)

/-- 最初の二正方形のそれぞれの包含。 -/
def firstTwoSquareInclusion (q : Fin 2) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ firstTwoSquarePasting :=
  ![pushout.inl (pastingSquareVertical.{u} 0) (pastingSquareVertical.{u} 0),
    pushout.inr (pastingSquareVertical.{u} 0) (pastingSquareVertical.{u} 0)] q

/-- 第三の正方形を貼る、中央の元の共有横辺。 -/
def threeSquareAttachingEdge : (Δ[1] : SSet.{u}) ⟶ firstTwoSquarePasting :=
  pastingSquareHorizontal 0 ≫ firstTwoSquareInclusion 1

/-- 二つの共有区間で貼り合わせた、元の三正方形の複体。 -/
def threeSquarePasting : SSet.{u} :=
  pushout (threeSquareAttachingEdge.{u}) (pastingSquareHorizontal.{u} 0)

/-- 元の三つの正方形の、それぞれの全体を含む射。 -/
def threeSquareInclusion (q : Fin 3) : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ threeSquarePasting :=
  ![firstTwoSquareInclusion 0 ≫
      pushout.inl (threeSquareAttachingEdge.{u}) (pastingSquareHorizontal.{u} 0),
    firstTwoSquareInclusion 1 ≫
      pushout.inl (threeSquareAttachingEdge.{u}) (pastingSquareHorizontal.{u} 0),
    pushout.inr (threeSquareAttachingEdge.{u}) (pastingSquareHorizontal.{u} 0)] q

/-- 最初と中央の正方形の元の共有縦辺は、貼り合わせ複体で厳密に一致する。 -/
lemma threeSquareInclusion_shared_first :
    pastingSquareVertical 0 ≫ threeSquareInclusion.{u} 0 =
      pastingSquareVertical 0 ≫ threeSquareInclusion 1 := by
  change pastingSquareVertical 0 ≫
      pushout.inl (pastingSquareVertical.{u} 0) (pastingSquareVertical.{u} 0) ≫
      pushout.inl (threeSquareAttachingEdge.{u}) (pastingSquareHorizontal.{u} 0) =
    pastingSquareVertical 0 ≫
      pushout.inr (pastingSquareVertical.{u} 0) (pastingSquareVertical.{u} 0) ≫
      pushout.inl (threeSquareAttachingEdge.{u}) (pastingSquareHorizontal.{u} 0)
  exact pushout.condition_assoc _

/-- 中央と最後の正方形の元の共有横辺も、貼り合わせ複体で厳密に一致する。 -/
lemma threeSquareInclusion_shared_second :
    pastingSquareHorizontal 0 ≫ threeSquareInclusion.{u} 1 =
      pastingSquareHorizontal 0 ≫ threeSquareInclusion 2 := by
  change pastingSquareHorizontal 0 ≫ firstTwoSquareInclusion 1 ≫
      pushout.inl (threeSquareAttachingEdge.{u}) (pastingSquareHorizontal.{u} 0) =
    pastingSquareHorizontal 0 ≫
      pushout.inr (threeSquareAttachingEdge.{u}) (pastingSquareHorizontal.{u} 0)
  exact pushout.condition
    (f := threeSquareAttachingEdge.{u}) (g := pastingSquareHorizontal.{u} 0)


variable {E : SSet.{u}} (q₀ q₁ q₂ : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ E)
  (h₁ : pastingSquareVertical 0 ≫ q₀ = pastingSquareVertical 0 ≫ q₁)
  (h₂ : pastingSquareHorizontal 0 ≫ q₁ = pastingSquareHorizontal 0 ≫ q₂)

/-- 同じ元の共有区間を持つ三正方形を、複体全体の実写像へ貼り合わせる。 -/
def threeSquarePastingMap : threeSquarePasting ⟶ E :=
  pushout.desc (f := threeSquareAttachingEdge.{u}) (g := pastingSquareHorizontal.{u} 0)
    (pushout.desc (f := pastingSquareVertical.{u} 0) (g := pastingSquareVertical.{u} 0) q₀ q₁ h₁)
    q₂ (by
      change (pastingSquareHorizontal 0 ≫
          pushout.inr (pastingSquareVertical.{u} 0) (pastingSquareVertical.{u} 0)) ≫ _ = _
      rw [Category.assoc, pushout.inr_desc]
      exact h₂)

/-- 貼り合わせた実写像は、元の各正方形の全体を厳密に回収する。 -/
lemma threeSquarePastingMap_inclusion (q : Fin 3) :
    threeSquareInclusion q ≫ threeSquarePastingMap q₀ q₁ q₂ h₁ h₂ = ![q₀, q₁, q₂] q := by
  fin_cases q
  · change (pushout.inl (pastingSquareVertical.{u} 0) (pastingSquareVertical.{u} 0) ≫
        pushout.inl (threeSquareAttachingEdge.{u}) (pastingSquareHorizontal.{u} 0)) ≫
        threeSquarePastingMap q₀ q₁ q₂ h₁ h₂ = q₀
    simp only [threeSquarePastingMap, Category.assoc, pushout.inl_desc]
  · change (pushout.inr (pastingSquareVertical.{u} 0) (pastingSquareVertical.{u} 0) ≫
        pushout.inl (threeSquareAttachingEdge.{u}) (pastingSquareHorizontal.{u} 0)) ≫
        threeSquarePastingMap q₀ q₁ q₂ h₁ h₂ = q₁
    simp only [threeSquarePastingMap, Category.assoc, pushout.inl_desc, pushout.inr_desc]
  · change pushout.inr (threeSquareAttachingEdge.{u}) (pastingSquareHorizontal.{u} 0) ≫
        threeSquarePastingMap q₀ q₁ q₂ h₁ h₂ = q₂
    exact pushout.inr_desc _ _ _

end SerrePositivity.KST.SConstruction
