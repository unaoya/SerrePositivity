module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeComponents
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.NerveInclusion

/-!
概要：実 cone の始頂点を除く面は、元の frame 図式の同じ通常単体である。
方針：後続埋め込みの全成分を通常分岐で回収し、元の閉 nerve の自然性を使う。
規約：実成分の全有限集合を比較する。使われ方：始頂点を含まない全 HA 方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.ComplexLimits
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_tail {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorConeData A X P Q c).pullback (Fin.succOrderEmb (n + 1)).toOrderHom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex
      (c ⋙ strictRawModuleTensorElementDiagram A X P Q)).toSimplexData := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
      (Fin.succ_injective _).injOn]
    have he := strictRawModuleTensorConeData_hom_ordinary A X P Q c (I.image Fin.succ)
      a.succ b.succ k (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two (Fin.succ_injective _).injOn hI)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min (Fin.succOrderEmb (n + 1)).monotone
        (by rw [ha]; exact I.isLeast_min' _) _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max (Fin.succOrderEmb (n + 1)).monotone
        (by rw [hb]; exact I.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injective _ (Fin.succ_injective _)]; exact hk) a.succ_ne_zero
    have hp := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveSimplex_pullback
        ((coneTailOrderHom n).monotone.functor ⋙ c ⋙
          strictRawModuleTensorElementDiagram A X P Q)
        (Fin.succOrderEmb (n + 1)).toOrderHom)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_data] at hp
    have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hom_heq_of_eq hp I a b k hI ha hb hk
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
      (Fin.succ_injective _).injOn] at hh
    exact eq_of_heq (he.trans hh.symm)

end SerrePositivity.EInfinity.BarrattEccles
