module

public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPrismZero
public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPrismNaturality
public import SerrePositivity.InfinityCategories.HomotopyLimits.NerveCoconePrism
public import SerrePositivity.InfinityCategories.Core.SliceMap

/-!
# 元の native prism の零端と通常右余錐の全円柱

概要：全混合単体の零端を元の通常右余錐の slice へ同定する。
方針：同じ通常余錐の有限単体表示と curry の厳密な逆性を使う。
規約：元の通常右脚の全円柱を保持する。
使われ方：native roof 全三角形の零端条件 hb。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
open CategoryTheory Limits SSet MonoidalCategory
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (C : RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

lemma simplex_zero_join {n : ℕ} (Γ : Fin (n + 1) ⥤ I) :
    (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
      (simplex C U p hp σ hU Γ (OrderHom.const _ 0)) =
    joinMap (SSet.yonedaEquiv.symm (show (nerve I) _⦋n⦌ from Γ)) (𝟙 (Δ[0] : SSet.{u})) ≫
      (SerrePositivity.InfinityCategories.F1B.nerveCoconeEquiv (rightCocone C U σ)).val ≫
        nerveToCoherent (KanHammockCategory C) := by
  rw [simplex_zero C U p hp σ hU Γ]
  have h := SSet.yonedaEquiv_symm_comp
    (show (nerve (KanHammockCategory C)) _⦋n + 1⦌ from
      FrameHom.TerminalCoconeSimplex.diagram (rightCocone C U σ) Γ)
    (nerveToCoherent (KanHammockCategory C))
  calc
    _ = ((joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
        (show (nerve (KanHammockCategory C)) _⦋n + 1⦌ from
          FrameHom.TerminalCoconeSimplex.diagram (rightCocone C U σ) Γ)) ≫
        nerveToCoherent (KanHammockCategory C) := by
      rw [Category.assoc, h]
      rfl
    _ = _ := by
      rw [FrameHom.TerminalCoconeSimplex.diagram_join, Category.assoc]

def rightSlice : nerve I ⟶ sliceOver (SSet.yonedaEquiv.symm
    (coherentNerveVertex ((kanHammockSourceFunctor C).obj Y))) :=
  sliceOverCurry ((SerrePositivity.InfinityCategories.F1B.nerveCoconeEquiv (rightCocone C U σ)).val ≫
    nerveToCoherent (KanHammockCategory C)) (by
      rw [← Category.assoc, SerrePositivity.InfinityCategories.F1B.nerveCocone_point]
      exact (SSet.yonedaEquiv_symm_comp
        (nerveVertex ((kanHammockSourceFunctor C).obj Y))
        (nerveToCoherent (KanHammockCategory C))).trans
          (congrArg (fun z : (SimplicialNerve (KanHammockCategory C)) _⦋0⦌ =>
            SSet.yonedaEquiv.symm z) (nerveToCoherent_vertex _)))

lemma prism_zero : prismEndpoint 0 (nerve I) ≫ prism C U p hp σ hU = rightSlice C U σ := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro Γ
  apply Subtype.ext
  exact simplex_zero_join C U p hp σ hU Γ

lemma prism_zero_uncurry :
    sliceOverUncurry (prismEndpoint 0 (nerve I) ≫ prism C U p hp σ hU) =
      (SerrePositivity.InfinityCategories.F1B.nerveCoconeEquiv (Cocone.mk Y σ)).val ≫ hammockLocalizationNerveMap C := by
  rw [prism_zero C U p hp σ hU]
  change sliceOverUncurry (sliceOverCurry _ _) = _
  rw [sliceOverUncurry_curry]
  change (SerrePositivity.InfinityCategories.F1B.nerveCoconeEquiv
    ((kanHammockSourceFunctor C).mapCocone (Cocone.mk Y σ))).val ≫ _ = _
  rw [← SerrePositivity.InfinityCategories.F1B.nerveCocone_mapCocone, Category.assoc]
  rfl

lemma prism_zero_evaluation :
    (β_ (nerve I) (Δ[1] : SSet.{u})).hom ≫ rightMappingSpacePrism (nerve I) ≫
      sliceOverUncurry (prismEndpoint 0 (nerve I) ≫ prism C U p hp σ hU) =
    (SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy σ).h ≫ hammockLocalizationNerveMap C := by
  rw [prism_zero_uncurry C U p hp σ hU]
  simpa only [Category.assoc] using congrArg (fun f => f ≫ hammockLocalizationNerveMap C)
    (FrameHom.nerveCoconePrism_eq_natTrans U (Cocone.mk Y σ))

end SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
