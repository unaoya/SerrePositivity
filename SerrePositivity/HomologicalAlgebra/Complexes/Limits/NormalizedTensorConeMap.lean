module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeMixedInjOn
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeDegeneratePullback
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeOrdinaryMap

/-!
概要：実 cone の始点付き任意作用素による pullback は、元の制限列の実 cone データに等しい。
方針：全対象と退化を含む全混合・通常成分の異種等号を、従属関数の外延性でまとめる。
規約：元の全データを保持する。使われ方：全次数の cone 単体の全自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeData_pullback_map {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom) =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · funext i
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_obj_prepend_map A X Y c θ i
  · apply Function.hfunext rfl
    intro I I' h
    cases h
    apply Function.hfunext rfl
    intro a a' h
    cases h
    apply Function.hfunext rfl
    intro b b' h
    cases h
    apply Function.hfunext rfl
    intro k k' h
    cases h
    apply Function.hfunext rfl
    intro hI hI' h
    cases h
    apply Function.hfunext rfl
    intro ha ha' h
    cases h
    apply Function.hfunext rfl
    intro hb hb' h
    cases h
    apply Function.hfunext rfl
    intro hk hk' h
    cases h
    by_cases ha0 : a = 0
    · have h0 : (0 : Fin (m + 2)) ∈ I := by rw [← ha0, ha]; exact I.min'_mem _
      by_cases hi : Set.InjOn θ.toOrderHom ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) : Set (Fin (m + 1)))
      · exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_pullback_hom_mixed_of_injOn
          A X Y c θ I a b k hI ha hb hk ha0 h0 hi
      · exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_pullback_hom_mixed_not_inj
          A X Y c θ I a b k hI ha hb hk ha0 h0 hi
    · exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_pullback_hom_ordinary_map A X Y c θ I a b k hI ha hb hk ha0

end SerrePositivity.ComplexLimits
