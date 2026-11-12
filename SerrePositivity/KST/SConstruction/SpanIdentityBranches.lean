module
public import SerrePositivity.KST.SConstruction.SpanPrisms

/-! # 恒等な枝を持つ span の族の厳密な認識
概要：一方の枝が始点で一定なら、元の span は標準恒等形状による引き戻し。
方針：二枝で射を比較する。
規約：単なるホモトピーによる一定性ではない。使われ方：ρ の二つの角の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：左枝が始点で一定な span は上枝に恒等な左枝を付けたもの。
方針：ホーンの二枝への制限で等号を検出する。
規約：入力の span を変更しない。使われ方：ρ の subobject の正規化。 -/
lemma spanFamily_constant_right {K D : SSet.{u}}
    (F : (horn 2 0 : SSet.{u}) ⊗ K ⟶ D) (L : (Δ[1] : SSet.{u}) ⊗ K ⟶ D)
    (f : K ⟶ D) (hL : (horn₂₀.ι₀₁ ▷ K) ≫ F = L)
    (hR : (horn₂₀.ι₀₂ ▷ K) ≫ F = snd (Δ[1] : SSet.{u}) K ≫ f)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ L = f) :
    F = (identitySpanShape true ▷ K) ≫ L := by
  have h₁ : horn₂₀.ι₀₁ ≫ identitySpanShape true = 𝟙 (Δ[1] : SSet.{u}) :=
    identitySpanSection_shape true
  have h₂ : horn₂₀.ι₀₂ ≫ identitySpanShape true =
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) : (Δ[1] : SSet.{u}) ⟶ Δ[1]) := by
    rw [identitySpanShape, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
    apply SSet.yonedaEquiv.injective
    decide
  apply spanPrisms_hom_ext
  · rw [hL, ← Category.assoc, ← comp_whiskerRight, h₁]
    simp
  · rw [hR, ← Category.assoc, ← comp_whiskerRight, h₂]
    have he : (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :
        (Δ[1] : SSet.{u}) ⟶ Δ[1]) ▷ K = snd (Δ[1] : SSet.{u}) K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K := rfl
    rw [he, Category.assoc, h₀]

/-- 概要：上枝が始点で一定な span は左枝に恒等な上枝を付けたもの。
方針：ホーンの二枝への制限で等号を検出する。
規約：全パラメーターでの等号。使われ方：ρ の quotient の正規化。 -/
lemma spanFamily_constant_left {K D : SSet.{u}}
    (F : (horn 2 0 : SSet.{u}) ⊗ K ⟶ D) (R : (Δ[1] : SSet.{u}) ⊗ K ⟶ D)
    (f : K ⟶ D) (hL : (horn₂₀.ι₀₁ ▷ K) ≫ F = snd (Δ[1] : SSet.{u}) K ≫ f)
    (hR : (horn₂₀.ι₀₂ ▷ K) ≫ F = R) (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ R = f) :
    F = (identitySpanShape false ▷ K) ≫ R := by
  have h₁ : horn₂₀.ι₀₂ ≫ identitySpanShape false = 𝟙 (Δ[1] : SSet.{u}) :=
    identitySpanSection_shape false
  have h₂ : horn₂₀.ι₀₁ ≫ identitySpanShape false =
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) : (Δ[1] : SSet.{u}) ⟶ Δ[1]) := by
    rw [identitySpanShape, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge]
    apply SSet.yonedaEquiv.injective
    decide
  apply spanPrisms_hom_ext
  · rw [hL, ← Category.assoc, ← comp_whiskerRight, h₂]
    have he : (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :
        (Δ[1] : SSet.{u}) ⟶ Δ[1]) ▷ K = snd (Δ[1] : SSet.{u}) K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K := rfl
    rw [he, Category.assoc, h₀]
  · rw [hR, ← Category.assoc, ← comp_whiskerRight, h₁]
    simp

end SerrePositivity.KST.SConstruction
