module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeMixedInjOn
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeDegeneratePullback
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeOrdinaryMap

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
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits
open _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorConeData_pullback_map {n m : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (θ : ⦋m⦌ ⟶ ⦋n⦌) :
    (strictRawModuleTensorConeData A X P Q c).pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ.toOrderHom) =
      strictRawModuleTensorConeData A X P Q
        ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · funext i
    exact strictRawModuleTensorConeData_obj_prepend_map A X P Q c θ i
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
      · exact strictRawModuleTensorConeData_pullback_hom_mixed_of_injOn
          A X P Q c θ I a b k hI ha hb hk ha0 h0 hi
      · exact strictRawModuleTensorConeData_pullback_hom_mixed_not_inj
          A X P Q c θ I a b k hI ha hb hk ha0 h0 hi
    · exact strictRawModuleTensorConeData_pullback_hom_ordinary_map A X P Q c θ I a b k hI ha hb hk ha0

end SerrePositivity.EInfinity.BarrattEccles
