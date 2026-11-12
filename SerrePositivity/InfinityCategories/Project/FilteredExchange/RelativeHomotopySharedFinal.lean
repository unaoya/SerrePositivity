module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ConvergentHomotopyHorn
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ConvergentTriangleInitialHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.DegenerateHomotopyTriangles
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeHornTensorExtension

/-!
概要：同じ終点を持つ二円柱の境界が同じ全円柱なら、境界固定で両始点を比較する。
方針：指定境界円柱の退化三角形を外ホーン充填で固定する。
規約：境界の定値性を全時刻の等式で返す。使われ方：相対持ち上げの境界移動の除去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：共通終点への同じ境界円柱を持つ比較は、始点間の境界固定比較を与える。
方針：二次外ホーンを退化境界三角形ごと充填。規約：有限性不要。使われ方：境界の厳密化。 -/
lemma exists_relativeHomotopySharedFinal {K X : SSet.{u}} [KanComplex X]
    (A : K.Subcomplex) {f₀ f₁ f₂ : K ⟶ X}
    (U : SSet.Homotopy f₀ f₂) (V : SSet.Homotopy f₁ f₂)
    (L : SSet.Homotopy (A.ι ≫ f₀) (A.ι ≫ f₂))
    (hU : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ U.h = L.h)
    (hV : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ V.h = L.h) :
    ∃ T : SSet.Homotopy f₀ f₁, (A.ι ▷ (Δ[1] : SSet.{u})) ≫ T.h =
      fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ f₀ := by
  let b := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle L 0
  have h₀ : (stdSimplex.δ (1 : Fin 3) ▷ (A : SSet.{u})) ≫ b =
      ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ U.h := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle_zero_long]
    change (β_ (Δ[1] : SSet.{u}) (A : SSet.{u})).hom ≫ L.h =
      (β_ (Δ[1] : SSet.{u}) (A : SSet.{u})).hom ≫
        ((A.ι ▷ (Δ[1] : SSet.{u})) ≫ U.h)
    rw [hU]
  have h₁ : (stdSimplex.δ (0 : Fin 3) ▷ (A : SSet.{u})) ≫ b =
      ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ V.h := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle_zero_last]
    change (β_ (Δ[1] : SSet.{u}) (A : SSet.{u})).hom ≫ L.h =
      (β_ (Δ[1] : SSet.{u}) (A : SSet.{u})).hom ≫
        ((A.ι ▷ (Δ[1] : SSet.{u})) ≫ V.h)
    rw [hV]
  have hw : ((horn 2 2).ι ▷ (A : SSet.{u})) ≫ b =
      ((horn 2 2 : SSet.{u}) ◁ A.ι) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.convergentHomotopyHorn U V := by
    apply (horn₂₂.isPushout.map (tensorRight (A : SSet.{u}))).hom_ext
    · change (horn₂₂.ι₀₂ ▷ (A : SSet.{u})) ≫
        (((horn 2 2).ι ▷ (A : SSet.{u})) ≫ b) = _
      rw [← comp_whiskerRight_assoc, horn.ι_ι]
      change (stdSimplex.δ (1 : Fin 3) ▷ (A : SSet.{u})) ≫ b =
        ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (horn₂₂.ι₀₂ ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.convergentHomotopyHorn U V
      rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.convergentHomotopyHorn_first]
      exact h₀
    · change (horn₂₂.ι₁₂ ▷ (A : SSet.{u})) ≫
        (((horn 2 2).ι ▷ (A : SSet.{u})) ≫ b) = _
      rw [← comp_whiskerRight_assoc, horn.ι_ι]
      change (stdSimplex.δ (0 : Fin 3) ▷ (A : SSet.{u})) ≫ b =
        ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (horn₂₂.ι₁₂ ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.convergentHomotopyHorn U V
      rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.convergentHomotopyHorn_last]
      exact h₁
  obtain ⟨F, hF, hA⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.exists_relativeHornTensorExtension A (2 : Fin 3)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.convergentHomotopyHorn U V) b hw
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.convergentTriangleInitialHomotopy U V F hF, ?_⟩
  change (β_ (A : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
    (stdSimplex.δ (2 : Fin 3) ▷ (A : SSet.{u})) ≫ (((Δ[2] : SSet.{u}) ◁ A.ι) ≫ F) = _
  rw [hA, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle_zero_first]
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
