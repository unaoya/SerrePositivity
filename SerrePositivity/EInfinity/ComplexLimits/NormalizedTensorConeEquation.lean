module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeInjectivePullback
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeLastEquation
public import SerrePositivity.EInfinity.ComplexLimits.ConeEquationTransfer

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open ConeHeadIndex
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorConeData_equation {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) : (normalizedTensorConeData A X Y c).Equation I := by
  by_cases h0 : (0 : Fin (n + 2)) ∈ I
  · intro a b k hI ha hb hk
    let J := withoutFirst I
    have hJ : J.Nonempty := withoutFirst_nonempty hI h0
    let r := J.card - 1
    have hc : J.card = r + 1 := by have := Finset.card_pos.mpr hJ; dsimp only [r]; omega
    let e := J.orderEmbOfFin hc
    let c' := (SimplexCategory.toCat.map (SimplexCategory.mkHom e.toOrderHom)).toFunctor ⋙ c
    have hp := normalizedTensorConeData_pullback_injective A X Y c e
    have ht := normalizedTensorConeData_equation_of_last_mem A X Y c'
      Finset.univ (Finset.mem_univ _)
    have heq := complexSimplexData_equation_image_of_pullback A
      (normalizedTensorConeData A X Y c) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom)
      (normalizedTensorConeData A X Y c') hp Finset.univ (prepend_injective e).injOn ht
    have h0U : (0 : Fin (n + 2)) ∈
        (Finset.univ : Finset (Fin (r + 2))).image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom) :=
      Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    have hu : withoutFirst (Finset.univ : Finset (Fin (r + 2))) = Finset.univ := by
      ext i
      simp [withoutFirst]
    have heU : (Finset.univ : Finset (Fin (r + 1))).image e = J :=
      J.image_orderEmbOfFin_univ hc
    have hImage : (Finset.univ : Finset (Fin (r + 2))).image
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom e.toOrderHom) = I := by
      rw [← withFirst_withoutFirst _ h0U, withoutFirst_image_prepend, hu, heU]
      exact withFirst_withoutFirst I h0
    rw [hImage] at heq
    exact heq a b k hI ha hb hk
  · exact normalizedTensorConeData_equation_without_zero A X Y c I h0

end SerrePositivity.EInfinity.ComplexLimits
