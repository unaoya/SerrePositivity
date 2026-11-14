module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.DegenerateHomotopyTriangles
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativeHomotopyComposite

/-!
概要：指定部分で片側が定値な円柱を合成し、他方の全円柱を保持する。
方針：指定部分に元の円柱の退化三角形を置き、相対ホーンを充填する。
規約：制限はホモトピー類ではなく射の等式。使われ方：相対比較の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：第一円柱が指定部分で定値なら、第二円柱の制限を保持して合成できる。
方針：σ₀ の退化三角形を固定する。規約：全時刻の一致。使われ方：近似と輸送の合成。 -/
lemma exists_relativeHomotopyComposite_left_constant {K X : SSet.{u}} [KanComplex X]
    (A : K.Subcomplex) {f₀ f₁ f₂ : K ⟶ X}
    (U : SSet.Homotopy f₀ f₁) (V : SSet.Homotopy f₁ f₂)
    (hU : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ U.h =
      fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ f₁) :
    ∃ T : SSet.Homotopy f₀ f₂,
      (A.ι ▷ (Δ[1] : SSet.{u})) ≫ T.h =
        (A.ι ▷ (Δ[1] : SSet.{u})) ≫ V.h := by
  let W := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp V A.ι
  have h₀ : (stdSimplex.δ (2 : Fin 3) ▷ (A : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle W 0 =
        ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ U.h := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle_zero_first]
    change _ = (β_ (Δ[1] : SSet.{u}) (A : SSet.{u})).hom ≫
      ((A.ι ▷ (Δ[1] : SSet.{u})) ≫ U.h)
    rw [hU]
    rfl
  have h₁ : (stdSimplex.δ (0 : Fin 3) ▷ (A : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle W 0 =
        ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ V.h := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle_zero_last]
    rfl
  obtain ⟨T, hT⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.exists_relativeHomotopyComposite A U V
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle W 0) h₀ h₁
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle_zero_long] at hT
  exact ⟨T, hT⟩

/-- 概要：第二円柱が指定部分で定値なら、第一円柱の制限を保持して合成できる。
方針：σ₁ の退化三角形を固定する。規約：全時刻の一致。使われ方：輸送と反映の合成。 -/
lemma exists_relativeHomotopyComposite_right_constant {K X : SSet.{u}} [KanComplex X]
    (A : K.Subcomplex) {f₀ f₁ f₂ : K ⟶ X}
    (U : SSet.Homotopy f₀ f₁) (V : SSet.Homotopy f₁ f₂)
    (hV : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ V.h =
      fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ f₁) :
    ∃ T : SSet.Homotopy f₀ f₂,
      (A.ι ▷ (Δ[1] : SSet.{u})) ≫ T.h =
        (A.ι ▷ (Δ[1] : SSet.{u})) ≫ U.h := by
  let W := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp U A.ι
  have h₀ : (stdSimplex.δ (2 : Fin 3) ▷ (A : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle W 1 =
        ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ U.h := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle_one_first]
    rfl
  have h₁ : (stdSimplex.δ (0 : Fin 3) ▷ (A : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle W 1 =
        ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ V.h := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle_one_last]
    change _ = (β_ (Δ[1] : SSet.{u}) (A : SSet.{u})).hom ≫
      ((A.ι ▷ (Δ[1] : SSet.{u})) ≫ V.h)
    rw [hV]
    rfl
  obtain ⟨T, hT⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.exists_relativeHomotopyComposite A U V
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle W 1) h₀ h₁
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.degenerateHomotopyTriangle_one_long] at hT
  exact ⟨T, hT⟩

end SerrePositivity.InfinityCategories.Project.FilteredExchange
