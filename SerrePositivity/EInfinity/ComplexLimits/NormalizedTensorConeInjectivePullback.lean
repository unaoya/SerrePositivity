module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeMixedPullback
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeOrdinaryPullback

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeData_pullback_injective {n m : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (e : Fin (m + 1) ↪o Fin (n + 1)) :
    (normalizedTensorConeData A X Y c).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom) =
      normalizedTensorConeData A X Y
        ((SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · funext i
    exact normalizedTensorConeData_obj_prepend A X Y c e i
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
      exact normalizedTensorConeData_pullback_hom_mixed A X Y c e I a b k hI ha hb hk ha0 h0
    · exact normalizedTensorConeData_pullback_hom_ordinary A X Y c e I a b k hI ha hb hk ha0

end SerrePositivity.EInfinity.ComplexLimits
