module

public import SerrePositivity.KST.Spectra.EnrichedOrderedCylinderBridge
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle

/-!
概要：豊穣自然変換の因子分解の三角形の外辺を、元の自然変換の円柱と照合する。
方針：三段から最初と最後を選び、二段の円柱から単位パラメータの円柱への比較を使う。
規約：全 Hom の厳密等式。使われ方：基点評価の coherent な辺を保持する貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.EnrichedTransformationTriangle
variable {C : Type v} {D : Type w} [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]
  (F G H : EnrichedFunctor SSet.{u} C D)
  (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
  (θ : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) G H)
  (ζ : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F H)
  (hc : ∀ X, ζ.app X = (λ_ (𝟙_ SSet.{u})).inv ≫
    (η.app X ⊗ₘ θ.app X) ≫ eComp SSet (F.obj X) (G.obj X) (H.obj X))

/-- 因子分解の三角形の外辺は、元の自然変換の二対象の円柱。 -/
lemma functor_outer :
    (EnrichedOrderedCylinder.reindex (C := C) (SimplexCategory.δ (1 : Fin 3)).toOrderHom).comp
        SSet (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedTransformationTriangle.functor F G H η θ ζ hc) =
      (EnrichedOrderedCylinder.bridge (C := C) (𝟙 (𝟙_ SSet.{u}))).comp SSet
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.evaluationFunctor (𝟙_ SSet.{u}) F H ζ) := by
  apply EnrichedFunctor.ext SSet
    (fun X ↦ by rcases X with ⟨j, x⟩; fin_cases j <;> rfl)
  rintro ⟨j, x⟩ ⟨k, y⟩
  fin_cases j <;> fin_cases k
  all_goals
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨p, f⟩
    solve
    | rfl
    | have hp := p.down.down
      norm_num [Fin.le_def] at hp

end SerrePositivity.KST.Spectra.EnrichedTransformationTriangle
