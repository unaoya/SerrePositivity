module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FixedInnerHornFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.InternalHomFlipAdjunction

/-!
概要：三つの指定面を持つパラメーター付き内三ホーンの実充填。
方針：積の族をパラメーターからの内部 Hom へ転置し、同じ三面を貼って充填する。
規約：三面の等式は厳密。欠面の全 native Hom についての追加条件は別に検証する。
使われ方：Ind-S (9b) の指定因子分解面の全族構成。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 右側のパラメーターを内部 Hom に移す、全族の転置。 -/
def familyRightTranspose (A K X : SSet.{u}) :
    (A ⊗ K ⟶ X) ≃ (A ⟶ (ihom K).obj X) :=
  ((ihom.adjunction A).homEquiv K X).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K A X)

/-- 転置は元の単体の任意の面・退化への制限と可換。 -/
lemma familyRightTranspose_precomp {A B K X : SSet.{u}} (i : A ⟶ B) (F : B ⊗ K ⟶ X) :
    familyRightTranspose A K X ((i ▷ K) ≫ F) = i ≫ familyRightTranspose B K X F := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K A X (curry ((i ▷ K) ≫ F)) =
    i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K B X (curry F)
  rw [← curry_pre_app, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app]

/-- 同じ三つの面の全族を保持する内ホーン Λ[3,2] の充填。 -/
lemma tetrahedronFamily_exists {X : SSet.{u}} [Quasicategory X] (K : SSet.{u})
    (F₀ F₁ F₃ : (Δ[2] : SSet.{u}) ⊗ K ⟶ X)
    (h₀₂ : (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ F₁ =
      (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ F₃)
    (h₁₂ : (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ F₀ =
      (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ F₃)
    (h₂₃ : (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ F₀ =
      (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ F₁) :
    ∃ F : (Δ[3] : SSet.{u}) ⊗ K ⟶ X,
      (stdSimplex.δ (0 : Fin 4) ▷ K) ≫ F = F₀ ∧
      (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ F = F₁ ∧
      (stdSimplex.δ (3 : Fin 4) ▷ K) ≫ F = F₃ := by
  let e₂ := familyRightTranspose (Δ[2] : SSet.{u}) K X
  have he₀₂ : stdSimplex.δ 2 ≫ e₂ F₁ = stdSimplex.δ 1 ≫ e₂ F₃ := by
    simpa only [e₂, familyRightTranspose_precomp] using congrArg (familyRightTranspose Δ[1] K X) h₀₂
  have he₁₂ : stdSimplex.δ 2 ≫ e₂ F₀ = stdSimplex.δ 0 ≫ e₂ F₃ := by
    simpa only [e₂, familyRightTranspose_precomp] using congrArg (familyRightTranspose Δ[1] K X) h₁₂
  have he₂₃ : stdSimplex.δ 0 ≫ e₂ F₀ = stdSimplex.δ 0 ≫ e₂ F₁ := by
    simpa only [e₂, familyRightTranspose_precomp] using congrArg (familyRightTranspose Δ[1] K X) h₂₃
  let a := horn₃₂.desc (e₂ F₀) (e₂ F₁) (e₂ F₃) he₀₂ he₁₂ he₂₃
  obtain ⟨f, hf⟩ := Quasicategory.hornFilling (S := (ihom K).obj X)
    (show 0 < (2 : Fin 4) by decide) (show (2 : Fin 4) < Fin.last 3 by decide) a
  let F := (familyRightTranspose Δ[3] K X).symm f
  have face (i : Fin 4) :
      familyRightTranspose Δ[2] K X ((stdSimplex.δ i ▷ K) ≫ F) = stdSimplex.δ i ≫ f := by
    rw [familyRightTranspose_precomp]
    exact congrArg (fun g => stdSimplex.δ i ≫ g)
      ((familyRightTranspose Δ[3] K X).apply_symm_apply f)
  refine ⟨F, e₂.injective ?_, e₂.injective ?_, e₂.injective ?_⟩
  · rw [show e₂ = familyRightTranspose Δ[2] K X from rfl, face]
    rw [← horn.ι_ι (2 : Fin 4) (0 : Fin 4) (by decide), Category.assoc, ← hf]
    exact horn₃₂.ι₀_desc _ _ _ _ _ _
  · rw [show e₂ = familyRightTranspose Δ[2] K X from rfl, face]
    rw [← horn.ι_ι (2 : Fin 4) (1 : Fin 4) (by decide), Category.assoc, ← hf]
    exact horn₃₂.ι₁_desc _ _ _ _ _ _
  · rw [show e₂ = familyRightTranspose Δ[2] K X from rfl, face]
    rw [← horn.ι_ι (2 : Fin 4) (3 : Fin 4) (by decide), Category.assoc, ← hf]
    exact horn₃₂.ι₃_desc _ _ _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
