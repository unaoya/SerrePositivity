module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativeHomotopyConstantComposition
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativeHomotopyConstantInverse

/-!
概要：両外側が指定部分で定値な比較の zigzag を、中央の全境界円柱を保って合成する。
方針：反映比較を相対反転し、退化三角形を固定して二回合成する。
規約：中央の円柱の制限に厳密に一致。使われ方：近似・輸送・反映の比較合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：外側が境界固定な三比較を合成し、中央の境界輸送を全時刻で保持する。
方針：相対反転と左右の定値合成。規約：有限性不要。使われ方：実際の引き戻し比較。 -/
lemma exists_relativeHomotopyZigzag {K X : SSet.{u}} [KanComplex X]
    (A : K.Subcomplex) {f₀ f₁ f₂ f₃ : K ⟶ X}
    (U : SSet.Homotopy f₀ f₁) (V : SSet.Homotopy f₁ f₂)
    (W : SSet.Homotopy f₃ f₂)
    (hU : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ U.h =
      fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ f₁)
    (hW : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ W.h =
      fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ f₃) :
    ∃ T : SSet.Homotopy f₀ f₃,
      (A.ι ▷ (Δ[1] : SSet.{u})) ≫ T.h =
        (A.ι ▷ (Δ[1] : SSet.{u})) ≫ V.h := by
  obtain ⟨R, hR⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.exists_relativeHomotopyConstantInverse A W hW
  have he : A.ι ≫ f₂ = A.ι ≫ f₃ := by
    have h := congrArg (fun r ↦ SSet.ι₁ ≫ r) hW
    rw [SSet.ι₁_comp_assoc, W.h₁] at h
    exact h
  have hR' : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ R.h =
      fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ f₂ := by
    rw [hR, he]
  obtain ⟨L, hL⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.exists_relativeHomotopyComposite_left_constant A U V hU
  obtain ⟨T, hT⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.exists_relativeHomotopyComposite_right_constant A L R hR'
  exact ⟨T, hT.trans hL⟩

end SerrePositivity.InfinityCategories.Project.FilteredExchange
