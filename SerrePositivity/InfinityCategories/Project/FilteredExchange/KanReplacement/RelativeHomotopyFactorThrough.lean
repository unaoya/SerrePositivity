module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.DegenerateHomotopyTriangles
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.ForkHomotopyHorn
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.ForkTriangleMissingHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativeHornTensorExtension

/-!
概要：境界固定の第一円柱を経由して、第二円柱を指定境界のまま因子分解する。
方針：指定境界円柱の退化三角形を外ホーン充填で固定する。
規約：境界の定値性を全時刻の等式で返す。使われ方：path 置換への厳密な境界充填。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：境界固定の第一円柱を経由する比較円柱は、第二円柱の全境界を保持して取れる。
方針：二次外ホーンを退化境界三角形ごと充填。規約：有限性不要。使われ方：指定 path を保つ終点射の持ち上げ。 -/
lemma exists_relativeHomotopyFactorThrough {K X : SSet.{u}} [KanComplex X]
    (A : K.Subcomplex) {f₀ f₁ f₂ : K ⟶ X}
    (U : SSet.Homotopy f₀ f₁) (V : SSet.Homotopy f₀ f₂)
    (L : SSet.Homotopy (A.ι ≫ f₀) (A.ι ≫ f₂))
    (hU : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ U.h =
      fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ f₀)
    (hV : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ V.h = L.h) :
    ∃ T : SSet.Homotopy f₁ f₂, (A.ι ▷ (Δ[1] : SSet.{u})) ≫ T.h = L.h := by
  let b := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle L 0
  have h₀ : (stdSimplex.δ (2 : Fin 3) ▷ (A : SSet.{u})) ≫ b =
      ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ U.h := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle_zero_first]
    change _ = (β_ (Δ[1] : SSet.{u}) (A : SSet.{u})).hom ≫
      ((A.ι ▷ (Δ[1] : SSet.{u})) ≫ U.h)
    rw [hU]
    rfl
  have h₁ : (stdSimplex.δ (1 : Fin 3) ▷ (A : SSet.{u})) ≫ b =
      ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ V.h := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle_zero_long]
    change (β_ (Δ[1] : SSet.{u}) (A : SSet.{u})).hom ≫ L.h =
      (β_ (Δ[1] : SSet.{u}) (A : SSet.{u})).hom ≫
        ((A.ι ▷ (Δ[1] : SSet.{u})) ≫ V.h)
    rw [hV]
  have hw : ((horn 2 0).ι ▷ (A : SSet.{u})) ≫ b =
      ((horn 2 0 : SSet.{u}) ◁ A.ι) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.forkHomotopyHorn U V := by
    apply (horn₂₀.isPushout.map (tensorRight (A : SSet.{u}))).hom_ext
    · change (horn₂₀.ι₀₁ ▷ (A : SSet.{u})) ≫
        (((horn 2 0).ι ▷ (A : SSet.{u})) ≫ b) = _
      rw [← comp_whiskerRight_assoc, horn.ι_ι]
      change (stdSimplex.δ (2 : Fin 3) ▷ (A : SSet.{u})) ≫ b =
        ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (horn₂₀.ι₀₁ ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.forkHomotopyHorn U V
      rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.forkHomotopyHorn_first]
      exact h₀
    · change (horn₂₀.ι₀₂ ▷ (A : SSet.{u})) ≫
        (((horn 2 0).ι ▷ (A : SSet.{u})) ≫ b) = _
      rw [← comp_whiskerRight_assoc, horn.ι_ι]
      change (stdSimplex.δ (1 : Fin 3) ▷ (A : SSet.{u})) ≫ b =
        ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (horn₂₀.ι₀₂ ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.forkHomotopyHorn U V
      rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.forkHomotopyHorn_last]
      exact h₁
  obtain ⟨F, hF, hA⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.exists_relativeHornTensorExtension A (0 : Fin 3)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.forkHomotopyHorn U V) b hw
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.forkTriangleMissingHomotopy U V F hF, ?_⟩
  change (β_ (A : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
    (stdSimplex.δ (0 : Fin 3) ▷ (A : SSet.{u})) ≫ (((Δ[2] : SSet.{u}) ◁ A.ι) ≫ F) = _
  rw [hA, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle_zero_last]
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
