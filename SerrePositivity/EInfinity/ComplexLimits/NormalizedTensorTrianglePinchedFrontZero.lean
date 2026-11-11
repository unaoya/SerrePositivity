module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleMixedLinear
public import SerrePositivity.EInfinity.ComplexLimits.ComplexConstantClosedSimplex

/-!
概要：元の pinched 単体の前面 cochain は非零次数で零になる。
方針：元の実 cochain・次数・部分集合と切断の一意性を使う。
規約：残る一項同士の比較は別工程。使われ方：大域評価三角形の混合 HA。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorTrianglePinched_obj_ne_two {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : τ i ≠ 2) :
    (normalizedTensorTrianglePinched A X Y c τ).obj i = X := by
  change ((normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c).val.obj
    (coneTriangleBackIndex τ i) = X
  rw [coneTriangleBackIndex_ne_two τ i hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.source_obj]

lemma normalizedTensorTrianglePinched_front_hom_zero {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbt : τ b ≠ 2) (hk0 : k ≠ 0) :
    (normalizedTensorTrianglePinched A X Y c τ).hom I a b k hI ha hb hk = 0 := by
  have hn : ∀ i ∈ I, τ i ≠ 2 := by
    intro i hi ht
    apply hbt
    have hib : i ≤ b := by rw [hb]; exact I.le_max' i hi
    exact le_antisymm (Fin.le_last _) (ht ▸ τ.monotone hib)
  let p := (normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c
  have he := simplexData_pullback_hom_eqOn p.val.toSimplexData
    (coneTriangleBackIndex τ) Fin.castSuccOrderEmb.toOrderHom I a b k hI ha hb hk
    (fun i hi => coneTriangleBackIndex_ne_two τ i (hn i hi))
  change HEq ((normalizedTensorTrianglePinched A X Y c τ).hom I a b k hI ha hb hk)
    ((p.val.pullback Fin.castSuccOrderEmb.toOrderHom).hom I a b k hI ha hb hk) at he
  have hs : p.val.pullback Fin.castSuccOrderEmb.toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := A) X).pullback (OrderHom.const _ (0 : Fin 1)) := p.source
  rw [hs, ← complexConstantClosedNerveSimplex A X] at he
  have hz : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex ((Functor.const (Fin (n + 1))).obj X ⋙ complexToClosed A)).hom
      I a b k hI ha hb hk = 0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_of_ne _ k hk0
  rw [hz] at he
  have haI : a ∈ I := by rw [ha]; exact I.min'_mem _
  exact eq_of_heq (he.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq
    (normalizedTensorTrianglePinched_obj_ne_two A X Y c τ a (hn a haI)).symm
    (normalizedTensorTrianglePinched_obj_ne_two A X Y c τ b hbt).symm rfl))

lemma normalizedTensorTrianglePinched_homOrZero_front_zero {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hbt : τ b ≠ 2) (hk0 : k ≠ 0) :
    (normalizedTensorTrianglePinched A X Y c τ).toSimplexData.homOrZero I a b k = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.homOrZero
  split_ifs with hI ha hb hk
  · exact normalizedTensorTrianglePinched_front_hom_zero A X Y c τ I a b k hI ha hb hk hbt hk0
  all_goals rfl
end SerrePositivity.EInfinity.ComplexLimits
