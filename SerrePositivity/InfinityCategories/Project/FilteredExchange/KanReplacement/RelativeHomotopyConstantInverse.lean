module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.ForkHomotopyHorn
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.ForkTriangleMissingHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativeHornTensorExtension

/-!
概要：指定部分で定値なホモトピーを、その定値境界を保って逆向きにする。
方針：元の円柱と定値円柱を外ホーンに貼り、定値部分三角形を固定して充填。
規約：境界は全時刻で固定。使われ方：有限模型からの反映比較の反転。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：定値な指定境界を厳密に保持する逆向きの円柱。
方針：二次外ホーンの欠けた辺を取る。規約：有限性不要。使われ方：相対反映の逆比較。 -/
lemma exists_relativeHomotopyConstantInverse {K X : SSet.{u}} [KanComplex X]
    (A : K.Subcomplex) {f g : K ⟶ X} (H : SSet.Homotopy f g)
    (hH : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ f) :
    ∃ T : SSet.Homotopy g f,
      (A.ι ▷ (Δ[1] : SSet.{u})) ≫ T.h =
        fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ f := by
  let V := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl f
  let b : (Δ[2] : SSet.{u}) ⊗ (A : SSet.{u}) ⟶ X :=
    snd (Δ[2] : SSet.{u}) (A : SSet.{u}) ≫ A.ι ≫ f
  have hb₀ : (stdSimplex.δ (2 : Fin 3) ▷ (A : SSet.{u})) ≫ b =
      ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h := by
    change snd (Δ[1] : SSet.{u}) (A : SSet.{u}) ≫ A.ι ≫ f =
      (β_ (Δ[1] : SSet.{u}) (A : SSet.{u})).hom ≫
        ((A.ι ▷ (Δ[1] : SSet.{u})) ≫ H.h)
    rw [hH]
    rfl
  have hb₁ : (stdSimplex.δ (1 : Fin 3) ▷ (A : SSet.{u})) ≫ b =
      ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (β_ (Δ[1] : SSet.{u}) K).hom ≫ V.h := by rfl
  have hw : ((horn 2 0).ι ▷ (A : SSet.{u})) ≫ b =
      ((horn 2 0 : SSet.{u}) ◁ A.ι) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.forkHomotopyHorn H V := by
    apply (horn₂₀.isPushout.map (tensorRight (A : SSet.{u}))).hom_ext
    · change (horn₂₀.ι₀₁ ▷ (A : SSet.{u})) ≫
        (((horn 2 0).ι ▷ (A : SSet.{u})) ≫ b) = _
      rw [← comp_whiskerRight_assoc, horn.ι_ι]
      change (stdSimplex.δ (2 : Fin 3) ▷ (A : SSet.{u})) ≫ b =
        ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (horn₂₀.ι₀₁ ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.forkHomotopyHorn H V
      rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.forkHomotopyHorn_first]
      exact hb₀
    · change (horn₂₀.ι₀₂ ▷ (A : SSet.{u})) ≫
        (((horn 2 0).ι ▷ (A : SSet.{u})) ≫ b) = _
      rw [← comp_whiskerRight_assoc, horn.ι_ι]
      change (stdSimplex.δ (1 : Fin 3) ▷ (A : SSet.{u})) ≫ b =
        ((Δ[1] : SSet.{u}) ◁ A.ι) ≫ (horn₂₀.ι₀₂ ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.forkHomotopyHorn H V
      rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.forkHomotopyHorn_last]
      exact hb₁
  obtain ⟨F, hF, hA⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.exists_relativeHornTensorExtension A (0 : Fin 3)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.forkHomotopyHorn H V) b hw
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.forkTriangleMissingHomotopy H V F hF, ?_⟩
  change (β_ (A : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
    (stdSimplex.δ (0 : Fin 3) ▷ (A : SSet.{u})) ≫ (((Δ[2] : SSet.{u}) ◁ A.ι) ≫ F) = _
  rw [hA]
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
