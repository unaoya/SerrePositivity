module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeOverNaturality
public import SerrePositivity.EInfinity.ComplexLimits.DoubleConeEndEdgeIndex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGSimplexComponentExt

/-!
概要：元の二重 cone の先端と終端を結ぶ実辺を、同じ恒等射の通常単体へ同定する。
方針：終端成分の実 augmentation を回収し、先端の恒等射を全一単体の等式へ戻す。
規約：HA Construction 1.3.1.6・1.3.1.13、対象と実辺全体の厳密な一致。使われ方：slice 内の最初の頂点の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.EInfinity.Modules SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorDoubleConeSimplex_end_edge {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorDoubleConeSimplex A X P Q c).pullback (doubleConeEndEdgeOrderHom n) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex ((Functor.const (Fin 2)).obj ((strictRawModuleProbeFunctor A X).obj P)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexData_ext_of_components A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
  · intro i
    fin_cases i
    · change moduleRightConeObj A (dgAlgebraCategory A ((assocForget A).obj X)) (strictRawModuleTensorConeSimplex A X P Q c) ((strictRawModuleProbeFunctor A X).obj P)
        (0 : Fin (n + 2)).castSucc = (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      rw [moduleRightConeObj_castSucc]
      rfl
    · exact strictRawModuleTensorDoubleConeSimplex_last A X P Q c
  · intro I a b k hI ha hb hk
    have hU := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.two_eq_univ I hI
    subst I
    have ha0 : a = 0 := ha.trans ((Finset.min'_eq_iff _ _ 0).2
      ⟨by simp, fun i _ => Fin.zero_le i⟩)
    have hb1 : b = 1 := hb.trans ((Finset.max'_eq_iff _ _ 1).2
      ⟨by simp, fun i _ => Fin.le_last i⟩)
    have hk0 : k = 0 := by simpa using hk
    subst ha0 hb1 hk0
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
      (doubleConeEndEdgeOrderHom_injective n).injOn]
    change HEq _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (𝟙 ((strictRawModuleProbeFunctor A X).obj P)) 0)
    have hII := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two (doubleConeEndEdgeOrderHom_injective n).injOn hI
    have he := moduleRightConeData_hom_last A (dgAlgebraCategory A ((assocForget A).obj X)) (strictRawModuleTensorConeSimplexAugmentation A X P Q c)
      (Finset.univ.image (doubleConeEndEdgeOrderHom n))
      (doubleConeEndEdgeOrderHom n 0) (doubleConeEndEdgeOrderHom n 1) 0 hII
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min (doubleConeEndEdgeOrderHom n).monotone
        (by rw [ha]; exact Finset.univ.isLeast_min' _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hII))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max (doubleConeEndEdgeOrderHom n).monotone
        (by rw [hb]; exact Finset.univ.isGreatest_max' _) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hII))
      (by rw [Finset.card_image_of_injective _ (doubleConeEndEdgeOrderHom_injective n)]; exact hk)
      (doubleConeEndEdgeOrderHom_one n)
    have hi0 : (Fin.last (n + 1)).predAboveOrderHom (doubleConeEndEdgeOrderHom n 0) = 0 := by
      rw [doubleConeEndEdgeOrderHom_zero]
      change (Fin.last (n + 1)).predAbove ((0 : Fin (n + 2)).castSucc) = 0
      exact Fin.predAbove_last_castSucc
    have ht : ∀ i j : Fin (n + 2), i = j →
        HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (strictRawModuleTensorConeAugmentationAt A X P Q c i) 0)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (strictRawModuleTensorConeAugmentationAt A X P Q c j) 0) := by
      intro i j h
      subst j
      rfl
    have hv := ht _ _ hi0
    change HEq _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom (𝟙 ((strictRawModuleProbeFunctor A X).obj P)) 0) at hv
    exact he.trans hv
end SerrePositivity.EInfinity.BarrattEccles
