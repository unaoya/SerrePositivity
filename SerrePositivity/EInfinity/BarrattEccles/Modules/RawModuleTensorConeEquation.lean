module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeInjectivePullback
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeLastEquation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EquationTransfer

/-!
概要：元の実 cone データの全有限集合・全次数の HA 方程式を証明する。
方針：始点を含む集合を昇順列へ選択し、その全頂点集合の終端方程式を元の集合へ移す。
規約：同じ元の実成分・符号を保持する。使われ方：全次数の実 cone 単体の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open _root_.SerrePositivity.ComplexLimits _root_.SerrePositivity.ComplexLimits.ConeHeadIndex
open SerrePositivity.InfinityCategories.HA.Section7_1_1
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma rawModuleSimplexData_equation_image_of_pullback {m n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) n) (α : Fin (m + 1) →o Fin (n + 1))
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) m) (h : s.pullback α = t)
    (J : Finset (Fin (m + 1))) (hi : Set.InjOn α (J : Set (Fin (m + 1))))
    (ht : t.Equation J) : s.Equation (J.image α) := by
  intro a b k hI ha hb hk
  have hcard : (J.image α).card = J.card := Finset.card_image_of_injOn hi
  have hJ : 2 ≤ J.card := by omega
  have hkJ : k = 2 - (J.card : ℤ) := by rwa [hcard] at hk
  let a' := J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
  let b' := J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
  have ha' : α a' = a := by
    rw [ha]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone (J.isLeast_min' _) _
  have hb' : α b' = b := by
    rw [hb]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone (J.isGreatest_max' _) _
  have hh := ht a' b' k hJ rfl rfl hkJ
  rw [← h] at hh
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullback_rhs_of_inj _ _ _ _ _ _ _ _ _ _ hi] at hh
  cases ha'
  cases hb'
  exact hh


lemma strictRawModuleTensorConeData_equation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (I : Finset (Fin (n + 2))) : (strictRawModuleTensorConeData A X P Q c).Equation I := by
  by_cases h0 : (0 : Fin (n + 2)) ∈ I
  · intro a b k hI ha hb hk
    let J := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I
    have hJ : J.Nonempty := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hI h0
    let r := J.card - 1
    have hc : J.card = r + 1 := by have := Finset.card_pos.mpr hJ; dsimp only [r]; omega
    let e := J.orderEmbOfFin hc
    let c' := (SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c
    have hp := strictRawModuleTensorConeData_pullback_injective A X P Q c e
    have ht := strictRawModuleTensorConeData_equation_of_last_mem A X P Q c'
      Finset.univ (Finset.mem_univ _)
    have heq := rawModuleSimplexData_equation_image_of_pullback A X
      (strictRawModuleTensorConeData A X P Q c) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom)
      (strictRawModuleTensorConeData A X P Q c') hp Finset.univ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.prepend_injective e).injOn ht
    have h0U : (0 : Fin (n + 2)) ∈
        (Finset.univ : Finset (Fin (r + 2))).image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom) :=
      Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    have hu : _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst (Finset.univ : Finset (Fin (r + 2))) = Finset.univ := by
      ext i
      simp [_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst]
    have heU : (Finset.univ : Finset (Fin (r + 1))).image e = J :=
      J.image_orderEmbOfFin_univ hc
    have hImage : (Finset.univ : Finset (Fin (r + 2))).image
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom) = I := by
      rw [← _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withFirst_withoutFirst _ h0U, _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_image_prepend, hu, heU]
      exact _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withFirst_withoutFirst I h0
    rw [hImage] at heq
    exact heq a b k hI ha hb hk
  · exact strictRawModuleTensorConeData_equation_without_zero A X P Q c I h0

end SerrePositivity.EInfinity.BarrattEccles
