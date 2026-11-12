module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# 充満忠実な関手の nerve の全単体の像

概要：全単体の射列が像に入ることを、元の全頂点が対象の像に入ることで特徴付ける。
方針：元の各頂点の原像を選び、充満性で全射を持ち上げ、忠実性で関手則を証明。
規約：対象の原像は同型だけではなく等式で指定する。
使われ方：語の包含による graph の像と二つの像の交わり。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (F : C ⥤ D) [F.Full] [F.Faithful] {n : SimplexCategoryᵒᵖ}

/-- 元の各頂点の等式による原像を使う、全射列の持ち上げ。 -/
def nerveChainLift (τ : (nerve D).obj n)
    (h : ∀ j, ∃ X : C, F.obj X = τ.obj j) : Fin (n.unop.len + 1) ⥤ C where
  obj j := Classical.choose (h j)
  map {i j} f := F.preimage (eqToHom (Classical.choose_spec (h i)) ≫ τ.map f ≫
    eqToHom (Classical.choose_spec (h j)).symm)
  map_id i := by
    apply F.map_injective
    simp
  map_comp f g := by
    apply F.map_injective
    simp [Category.assoc]

lemma nerveChainLift_comp (τ : (nerve D).obj n) (h : ∀ j, ∃ X : C, F.obj X = τ.obj j) :
    nerveChainLift F τ h ⋙ F = τ := by
  apply Functor.hext (fun j => Classical.choose_spec (h j))
  intro i j f
  change HEq (F.map (F.preimage _)) (τ.map f)
  rw [F.map_preimage]
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

/-- 充満忠実な関手の nerve の像は、全頂点の対象の像で特徴付けられる。 -/
lemma nerveMap_range_iff (τ : (nerve D).obj n) :
    τ ∈ Set.range ((nerveMap F).app n) ↔ ∀ j, τ.obj j ∈ Set.range F.obj := by
  constructor
  · rintro ⟨σ, rfl⟩ j
    exact ⟨σ.obj j, rfl⟩
  · intro h
    exact ⟨nerveChainLift F τ h, nerveChainLift_comp F τ h⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
