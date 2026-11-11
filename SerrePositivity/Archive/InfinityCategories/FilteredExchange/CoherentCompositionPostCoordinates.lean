module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionSimplex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionCoordinates

/-!
概要：元の合成単体の最後への Hom の座標と、同じ固定射の後合成を照合する。
方針：豊穣合成の後合成則と Yoneda の自然性を元の座標へ代入する。
規約：二つの全 Hom 単体と切替ラベルを保持。使われ方：元の合成 prism の終域自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {X Y Z W : C} {n : ℕ}
  (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
  (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (g : Z ⟶ W)
  (t : Fin (n + 1) →o Fin 2)
local notation "τg" => NatTrans.app (eHomWhiskerLeft SSet Y g) (Opposite.op ⦋n⦌) τ

/-- 同じ Hom 単体の後合成は、元の Yoneda 射への後合成である。 -/
lemma simplicialHom_yoneda_post :
    SSet.yonedaEquiv.symm τg = SSet.yonedaEquiv.symm τ ≫ eHomWhiskerLeft SSet Y g := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- 零ラベルから最後への二因子の指定値は、同じ第二射の後合成と整合する。 -/
lemma coherentCompositionHom_zero_last_post (i : Fin (n + 1)) (hi : t i = 0) :
    (coherentCompositionHom σ τ t i.castSucc (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentCompositionObj_zero X Y Z t i hi) (coherentCompositionObj_last X Y Z n t))) ≫
        eHomWhiskerLeft SSet X g =
    coherentCompositionHom σ τg t i.castSucc (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentCompositionObj_zero X Y W t i hi) (coherentCompositionObj_last X Y W n t)) := by
  rw [coherentCompositionHom_zero_last σ τ t i hi,
    coherentCompositionHom_zero_last σ τg t i hi, simplicialHom_yoneda_post τ g,
    Category.assoc, eComp_eHomWhiskerLeft, ← Category.assoc, lift_whiskerLeft]
  simp only [Category.assoc]

/-- 一ラベルから最後への指定値も、同じ第二射の後合成と整合する。 -/
lemma coherentCompositionHom_one_last_post (i : Fin (n + 1)) (hi : t i ≠ 0) :
    (coherentCompositionHom σ τ t i.castSucc (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentCompositionObj_one X Y Z t i hi) (coherentCompositionObj_last X Y Z n t))) ≫
        eHomWhiskerLeft SSet Y g =
    coherentCompositionHom σ τg t i.castSucc (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentCompositionObj_one X Y W t i hi) (coherentCompositionObj_last X Y W n t)) := by
  rw [coherentCompositionHom_one_last σ τ t i hi,
    coherentCompositionHom_one_last σ τg t i hi, simplicialHom_yoneda_post τ g, Category.assoc]

end SerrePositivity.InfinityCategories.F2
