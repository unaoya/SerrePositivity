module

public import SerrePositivity.InfinityCategories.F2.IntervalPullbackBoundarySquare
public import SerrePositivity.InfinityCategories.F2.KanCospanPathEndpoints

/-!
概要：元の二入力の輸送に整合する Kan path 正方形を、Kan 引き戻し内の比較へ移す。
方針：単位の自然性で三座標を揃え、指定全境界正方形を引き戻しへ持ち上げる。
規約：元の二入力の円柱を単位で写した全円柱を保持する。
使われ方：有限 path 模型の同時輸送から標的引き戻し内の実際のホモトピーへ進む。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の境界輸送を持つ Kan 正方形を、三座標を保つ実際の引き戻し比較へ移す。
方針：二入力の円柱を単位で写し、境界の後合成式と単位の自然性を使う。
規約：有限性や充填性を元の値に要求しない。使われ方：標的側の指定 path の輸送。 -/
lemma kanCospan_pullback_homotopy_of_square {K E D X : SSet.{u}}
    (f : E ⟶ X) (g : D ⟶ X) {u₀ u₁ : K ⟶ E} {v₀ v₁ : K ⟶ D}
    (H₀ : SSet.Homotopy (u₀ ≫ f ≫ continuousKanReplacementUnit.app X)
      (v₀ ≫ g ≫ continuousKanReplacementUnit.app X))
    (U : SSet.Homotopy u₀ u₁) (V : SSet.Homotopy v₀ v₁)
    {b : K ⊗ (Δ[1] : SSet.{u}) ⟶ continuousKanReplacement.obj X}
    (G : SSet.Homotopy H₀.h b)
    (hG : (cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫ G.h =
      coprodCylinderMap (U.h ≫ f) (V.h ≫ g) ≫ continuousKanReplacementUnit.app X) :
    ∃ H₁ : SSet.Homotopy
      ((u₁ ≫ continuousKanReplacementUnit.app E) ≫ continuousKanReplacement.map f)
      ((v₁ ≫ continuousKanReplacementUnit.app D) ≫ continuousKanReplacement.map g), H₁.h = b ∧
      ∃ L : SSet.Homotopy
        (intervalPullbackHomotopyPoint (continuousKanReplacement.map f)
          (continuousKanReplacement.map g) (u₀ ≫ continuousKanReplacementUnit.app E)
          (v₀ ≫ continuousKanReplacementUnit.app D) (kanCospanUnitPath f g u₀ v₀ H₀))
        (intervalPullbackHomotopyPoint (continuousKanReplacement.map f)
          (continuousKanReplacement.map g) (u₁ ≫ continuousKanReplacementUnit.app E)
          (v₁ ≫ continuousKanReplacementUnit.app D) H₁),
        L.h ≫ intervalPullbackLeft (continuousKanReplacement.map f)
          (continuousKanReplacement.map g) = U.h ≫ continuousKanReplacementUnit.app E ∧
        L.h ≫ intervalPullbackRight (continuousKanReplacement.map f)
          (continuousKanReplacement.map g) = V.h ≫ continuousKanReplacementUnit.app D ∧
        L.h ≫ intervalPullbackPath (continuousKanReplacement.map f)
          (continuousKanReplacement.map g) = pathSquareCurry G.h := by
  have hf : f ≫ continuousKanReplacementUnit.app X =
      continuousKanReplacementUnit.app E ≫ continuousKanReplacement.map f :=
    continuousKanReplacementUnit.naturality f
  have hg : g ≫ continuousKanReplacementUnit.app X =
      continuousKanReplacementUnit.app D ≫ continuousKanReplacement.map g :=
    continuousKanReplacementUnit.naturality g
  have h : (cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫ G.h =
      coprodCylinderMap ((U.h ≫ continuousKanReplacementUnit.app E) ≫
        continuousKanReplacement.map f) ((V.h ≫ continuousKanReplacementUnit.app D) ≫
          continuousKanReplacement.map g) := by
    rw [hG, coprodCylinderMap_comp]
    simp only [Category.assoc, hf, hg]
  exact intervalPullback_homotopy_of_boundary_square (continuousKanReplacement.map f)
    (continuousKanReplacement.map g) (kanCospanUnitPath f g u₀ v₀ H₀)
    (functorHomotopyPostcomp U (continuousKanReplacementUnit.app E))
    (functorHomotopyPostcomp V (continuousKanReplacementUnit.app D)) G h

end SerrePositivity.InfinityCategories.F2
