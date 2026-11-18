module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeMixedPullback
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeOrdinaryPullback

/-!
概要：実 cone の始点付き単射による pullback は、元の制限列の実 cone データに等しい。
方針：全対象と全混合・通常成分の異種等号を、従属関数の外延性でまとめる。
規約：元の全データを保持する。使われ方：任意終端への HA 方程式の移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeData_pullback_injective {n m : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y c).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom) =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData A X Y
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · funext i
    exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_obj_prepend A X Y c e i
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
      exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_pullback_hom_mixed A X Y c e I a b k hI ha hb hk ha0 h0
    · exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConeData_pullback_hom_ordinary A X Y c e I a b k hI ha hb hk ha0

end SerrePositivity.ComplexLimits
