module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTrianglePostOverPreEvaluation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopyRelativePost
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TetrahedronComparisonReindexReflection

/-!
概要：元の六 native 作用と四面の指定三角形比較を、全始域の底上の制限に沿って保持する。
方針：六辺の厳密な交換と四面の指定成分の自然性を同じ制限データへ束ねる。
規約：元の指定値を再選択しない。使われ方：三つの全選択族の指定関係を共通全空間へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B C D : SSet.{u + 1}} {F₀ F₁ F₂ F₃ : B ⟶ SpaceInfinity.{u}}
  {a₀₁ : SSet.Homotopy F₀ F₁} {a₁₂ : SSet.Homotopy F₁ F₂} {a₂₃ : SSet.Homotopy F₂ F₃}
  {a₀₂ : SSet.Homotopy F₀ F₂} {a₁₃ : SSet.Homotopy F₁ F₃} {a₀₃ : SSet.Homotopy F₀ F₃}
  (T₀₁₂ : FunctorCompositionTriangle a₀₁ a₁₂ a₀₂)
  (T₁₂₃ : FunctorCompositionTriangle a₁₂ a₂₃ a₁₃)
  (T₀₁₃ : FunctorCompositionTriangle a₀₁ a₁₃ a₀₃)
  (T₀₂₃ : FunctorCompositionTriangle a₀₂ a₂₃ a₀₃)
  (p : C ⟶ B) (d : D ⟶ B) (t : D ⟶ C) (ht : t ≫ p = d)

/-- 元の全六辺と全四面の指定比較は、底上の同じ制限に沿って全次数で自然。 -/
def functorTetrahedronPostComparisonReindex : TetrahedronComparisonReindex
    (relativeFunctorSpace (leftUnstraighteningProjection F₀) p)
    (relativeFunctorSpace (leftUnstraighteningProjection F₁) p)
    (relativeFunctorSpace (leftUnstraighteningProjection F₂) p)
    (relativeFunctorSpace (leftUnstraighteningProjection F₃) p)
    (relativeFunctorSpace (leftUnstraighteningProjection F₀) d)
    (relativeFunctorSpace (leftUnstraighteningProjection F₁) d)
    (relativeFunctorSpace (leftUnstraighteningProjection F₂) d)
    (relativeFunctorSpace (leftUnstraighteningProjection F₃) d) where
  old01 := functorHomotopyRelativePost a₀₁ p
  old12 := functorHomotopyRelativePost a₁₂ p
  old23 := functorHomotopyRelativePost a₂₃ p
  old02 := functorHomotopyRelativePost a₀₂ p
  old13 := functorHomotopyRelativePost a₁₃ p
  old03 := functorHomotopyRelativePost a₀₃ p
  new01 := functorHomotopyRelativePost a₀₁ d
  new12 := functorHomotopyRelativePost a₁₂ d
  new23 := functorHomotopyRelativePost a₂₃ d
  new02 := functorHomotopyRelativePost a₀₂ d
  new13 := functorHomotopyRelativePost a₁₃ d
  new03 := functorHomotopyRelativePost a₀₃ d
  r0 := relativeFunctorOverPre (leftUnstraighteningProjection F₀)
    (Over.homMk (U := Over.mk d) (V := Over.mk p) t ht)
  r1 := relativeFunctorOverPre (leftUnstraighteningProjection F₁)
    (Over.homMk (U := Over.mk d) (V := Over.mk p) t ht)
  r2 := relativeFunctorOverPre (leftUnstraighteningProjection F₂)
    (Over.homMk (U := Over.mk d) (V := Over.mk p) t ht)
  r3 := relativeFunctorOverPre (leftUnstraighteningProjection F₃)
    (Over.homMk (U := Over.mk d) (V := Over.mk p) t ht)
  old012 := functorTriangleSequentialPostComparison T₀₁₂ p
  old123 := functorTriangleSequentialPostComparison T₁₂₃ p
  old013 := functorTriangleSequentialPostComparison T₀₁₃ p
  old023 := functorTriangleSequentialPostComparison T₀₂₃ p
  new012 := functorTriangleSequentialPostComparison T₀₁₂ d
  new123 := functorTriangleSequentialPostComparison T₁₂₃ d
  new013 := functorTriangleSequentialPostComparison T₀₁₃ d
  new023 := functorTriangleSequentialPostComparison T₀₂₃ d
  comm01 := ⟨relativeFunctorPost_overPre p d _ _ t ht _ _⟩
  comm12 := ⟨relativeFunctorPost_overPre p d _ _ t ht _ _⟩
  comm23 := ⟨relativeFunctorPost_overPre p d _ _ t ht _ _⟩
  comm02 := ⟨relativeFunctorPost_overPre p d _ _ t ht _ _⟩
  comm13 := ⟨relativeFunctorPost_overPre p d _ _ t ht _ _⟩
  comm03 := ⟨relativeFunctorPost_overPre p d _ _ t ht _ _⟩
  value012 := functorTriangleSequentialPostComparison_overPre_app_heq T₀₁₂ p d t ht
  value123 := functorTriangleSequentialPostComparison_overPre_app_heq T₁₂₃ p d t ht
  value013 := functorTriangleSequentialPostComparison_overPre_app_heq T₀₁₃ p d t ht
  value023 := functorTriangleSequentialPostComparison_overPre_app_heq T₀₂₃ p d t ht

end SerrePositivity.InfinityCategories.F2
