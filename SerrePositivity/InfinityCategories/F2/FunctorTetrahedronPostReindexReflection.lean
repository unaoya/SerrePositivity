module

public import SerrePositivity.InfinityCategories.F2.FunctorTetrahedronPostReindex

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
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C D : SSet.{u + 1}} {F₀ F₁ F₂ F₃ : B ⟶ SpaceInfinity.{u}}
  {a₀₁ : SSet.Homotopy F₀ F₁} {a₁₂ : SSet.Homotopy F₁ F₂} {a₂₃ : SSet.Homotopy F₂ F₃}
  {a₀₂ : SSet.Homotopy F₀ F₂} {a₁₃ : SSet.Homotopy F₁ F₃} {a₀₃ : SSet.Homotopy F₀ F₃}
  (T₀₁₂ : FunctorCompositionTriangle a₀₁ a₁₂ a₀₂)
  (T₁₂₃ : FunctorCompositionTriangle a₁₂ a₂₃ a₁₃)
  (T₀₁₃ : FunctorCompositionTriangle a₀₁ a₁₃ a₀₃)
  (T₀₂₃ : FunctorCompositionTriangle a₀₂ a₂₃ a₀₃)
  (p : C ⟶ B) (d : D ⟶ B) (t : D ⟶ C) (ht : t ≫ p = d)

local notation "R" => functorTetrahedronPostComparisonReindex T₀₁₂ T₁₂₃ T₀₁₃ T₀₂₃ p d t ht

/-- 切断を持つ底上の制限先での元の四面の指定関係は、元の全相対始域へ反映される。 -/
lemma functorTetrahedronPostComparison_square_of_reindexed
    (s : C ⟶ D) (hs : s ≫ d = p) (hst : s ≫ t = 𝟙 C)
    (x : (relativeFunctorSpace (leftUnstraighteningProjection F₀) p) _⦋0⦌)
    (h : (R).new013.app ((R).r0.app _ x) ≪≫
        (R).new123.app ((R).new01.app _ ((R).r0.app _ x)) =
      (R).new023.app ((R).r0.app _ x) ≪≫
        VertexIso.map ((R).new012.app ((R).r0.app _ x)) (R).new23) :
    (R).old013.app x ≪≫ (R).old123.app ((R).old01.app _ x) =
      (R).old023.app x ≪≫ VertexIso.map ((R).old012.app x) (R).old23 := by
  let f : Over.mk d ⟶ Over.mk p := Over.homMk t ht
  let g : Over.mk p ⟶ Over.mk d := Over.homMk s hs
  have hg : g ≫ f = 𝟙 (Over.mk p) := by
    apply Over.OverMorphism.ext
    exact hst
  have hr : (R).r3 ≫ relativeFunctorOverPre (leftUnstraighteningProjection F₃) g =
      𝟙 (relativeFunctorSpace (leftUnstraighteningProjection F₃) p) := by
    change relativeFunctorOverPre (leftUnstraighteningProjection F₃) f ≫ _ = _
    rw [← relativeFunctorOverPre_comp, hg, relativeFunctorOverPre_id]
    rfl
  exact (R).square_of_reindexed _ hr x h

end SerrePositivity.InfinityCategories.F2
