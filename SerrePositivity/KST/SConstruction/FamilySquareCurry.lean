module
public import SerrePositivity.KST.SConstruction.MappingSquareUncurry
public import SerrePositivity.KST.SConstruction.MappingSquareBoundaryData

/-! # 元の二次元円柱の全四辺を保つ内部 Hom 正方形
概要：二時刻の実写像を内部 Hom の正方形に移し、四辺を同じ円柱として回収する。
方針：結合子の逆と curry を使い、既存の uncurry の四面公式で証明する。
規約：元の実写像を変更せず、全パラメータ・全時刻を保持する。
使われ方：貼り合わせた全交換セルの辺路の合成関係。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 任意の元の円柱を、元の二端面を持つ実ホモトピーとして読む。 -/
def familyCylinder {U E : SSet.{u}} (h : U ⊗ (Δ[1] : SSet.{u}) ⟶ E) :
    SSet.Homotopy (SSet.ι₀ ≫ h) (SSet.ι₁ ≫ h) where
  h := h
  h₀ := rfl
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 元の二時刻の全写像を内部 Hom の同じ全正方形に移す。 -/
def familySquareCurry {U E : SSet.{u}}
    (q : (U ⊗ (Δ[1] : SSet.{u})) ⊗ Δ[1] ⟶ E) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom U).obj E :=
  curry ((α_ U Δ[1] Δ[1]).inv ≫ q)

/-- 復号すると元の全二次元円柱そのものを回収する。 -/
lemma mappingSquareUncurry_familySquareCurry {U E : SSet.{u}}
    (q : (U ⊗ (Δ[1] : SSet.{u})) ⊗ Δ[1] ⟶ E) :
    mappingSquareUncurry (familySquareCurry q) = q := by
  simp only [mappingSquareUncurry, familySquareCurry, uncurry_curry,
    Iso.hom_inv_id_assoc]

/-- 零横辺は元の零時刻の円柱全体。 -/
lemma familySquareCurry_zero {U E : SSet.{u}}
    (q : (U ⊗ (Δ[1] : SSet.{u})) ⊗ Δ[1] ⟶ E) :
    SSet.ι₀ ≫ familySquareCurry q = curry (SSet.ι₀ ≫ q) := by
  apply uncurry_injective
  rw [← mappingSquareUncurry_zero, mappingSquareUncurry_familySquareCurry, uncurry_curry]

/-- 一横辺も元の一時刻の円柱全体。 -/
lemma familySquareCurry_one {U E : SSet.{u}}
    (q : (U ⊗ (Δ[1] : SSet.{u})) ⊗ Δ[1] ⟶ E) :
    SSet.ι₁ ≫ familySquareCurry q = curry (SSet.ι₁ ≫ q) := by
  apply uncurry_injective
  rw [← mappingSquareUncurry_one, mappingSquareUncurry_familySquareCurry, uncurry_curry]

/-- 左辺は元の始点側の全時間区間。 -/
lemma familySquareCurry_source {U E : SSet.{u}}
    (q : (U ⊗ (Δ[1] : SSet.{u})) ⊗ Δ[1] ⟶ E) :
    pastingSquareVertical 0 ≫ familySquareCurry q =
      curry ((SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ q) := by
  apply uncurry_injective
  rw [← mappingSquareUncurry_source, mappingSquareUncurry_familySquareCurry, uncurry_curry]

/-- 右辺も元の終点側の全時間区間。 -/
lemma familySquareCurry_target {U E : SSet.{u}}
    (q : (U ⊗ (Δ[1] : SSet.{u})) ⊗ Δ[1] ⟶ E) :
    pastingSquareVertical 1 ≫ familySquareCurry q =
      curry ((SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ q) := by
  apply uncurry_injective
  rw [← mappingSquareUncurry_target, mappingSquareUncurry_familySquareCurry, uncurry_curry]

end SerrePositivity.KST.SConstruction
