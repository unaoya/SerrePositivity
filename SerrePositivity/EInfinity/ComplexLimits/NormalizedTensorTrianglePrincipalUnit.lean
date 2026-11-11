module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTrianglePrincipalPinched
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTrianglePinchedFrontZero

/-!
概要：元の主切断の評価・単位合成と符号から、同じ中央相の全切断和を比較する。
方針：元の二つの切断・実評価成分・全添字と次数を保持する。
規約：全二次境界と混合 HA は別工程。使われ方：大域評価三角形の実三相単体。
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

lemma normalizedTensorTrianglePinched_front_hom_unit {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : (0 : ℤ) = 2 - (I.card : ℤ)) (hbt : τ b ≠ 2) :
    HEq ((normalizedTensorTrianglePinched A X Y c τ).hom I a b 0 hI ha hb hk)
      (unitElement A X).val := by
  have hn : ∀ i ∈ I, τ i ≠ 2 := by
    intro i hi ht
    apply hbt
    have hib : i ≤ b := by rw [hb]; exact I.le_max' i hi
    exact le_antisymm (Fin.le_last _) (ht ▸ τ.monotone hib)
  let p := (normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c
  have he := simplexData_pullback_hom_eqOn p.val.toSimplexData
    (coneTriangleBackIndex τ) Fin.castSuccOrderEmb.toOrderHom I a b 0 hI ha hb hk
    (fun i hi => coneTriangleBackIndex_ne_two τ i (hn i hi))
  change HEq ((normalizedTensorTrianglePinched A X Y c τ).hom I a b 0 hI ha hb hk)
    ((p.val.pullback Fin.castSuccOrderEmb.toOrderHom).hom I a b 0 hI ha hb hk) at he
  have hs : p.val.pullback Fin.castSuccOrderEmb.toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := A) X).pullback (OrderHom.const _ (0 : Fin 1)) := p.source
  rw [hs] at he
  have hni : ¬ Set.InjOn (OrderHom.const (Fin (n + 1)) (0 : Fin 1)) (I : Set (Fin (n + 1))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.not_injOn_constant hI
  exact he.trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := A) X).toSimplexData.pullback_hom_of_collapsed_pair
    _ I a b 0 hI ha hb hk hni (by omega))

lemma normalizedTensorTrianglePinched_principal_composite {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (τ : Fin (n + 1) →o Fin 3) (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (hs1 : τ (ConeHeadIndex.second I hI) = 1)
    (hp1 : τ (ConeHeadIndex.penultimate I hI) = 1)
    (haz : τ (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 0)
    (hbt : τ (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 2)
    (L R : Finset (Fin (n + 1))) (hRset : R = I.filter (ConeHeadIndex.second I hI ≤ ·))
    (k : ℤ) (hL : 2 ≤ L.card)
    (hLa : I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) = L.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL))
    (hLs : ConeHeadIndex.second I hI = L.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hL))
    (hkL : (0 : ℤ) = 2 - (L.card : ℤ)) (hR : 2 ≤ R.card)
    (hRs : ConeHeadIndex.second I hI = R.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hR))
    (hRb : I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) = R.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hR))
    (hkR : k = 2 - (R.card : ℤ)) (hJ : (I.filter (fun i => τ i = 1)).Nonempty)
    (hkJ : k = 1 - ((I.filter (fun i => τ i = 1)).card : ℤ)) :
    HEq (compose A
      ((normalizedTensorTrianglePinched A X Y c τ).hom R (ConeHeadIndex.second I hI)
        (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) k hR hRs hRb hkR)
      ((normalizedTensorTrianglePinched A X Y c τ).hom L (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
        (ConeHeadIndex.second I hI) 0 hL hLa hLs hkL) (zero_add k))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex
        ((normalizedTensorElementPinchedMap A X Y).app (Opposite.op ⦋n⦌) c)).val.component
          (I.filter (fun i => τ i = 1)) k hJ hkJ) := by
  have ha2 : τ (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) ≠ 2 := by rw [haz]; decide
  have hs2 : τ (ConeHeadIndex.second I hI) ≠ 2 := by rw [hs1]; decide
  have hsx := normalizedTensorTrianglePinched_obj_ne_two A X Y c τ _ hs2
  have hax := normalizedTensorTrianglePinched_obj_ne_two A X Y c τ _ ha2
  have hl := normalizedTensorTrianglePinched_front_hom_unit A X Y c τ L
    (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (ConeHeadIndex.second I hI) hL hLa hLs hkL hs2
  have hu : HEq (unitElement A X).val
      (unitElement A ((normalizedTensorTrianglePinched A X Y c τ).obj
        (ConeHeadIndex.second I hI))).val := by rw [hsx]
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_unit_of_heq
    ((normalizedTensorTrianglePinched A X Y c τ).hom R (ConeHeadIndex.second I hI)
      (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) k hR hRs hRb hkR)
    _ (zero_add k) (hax.trans hsx.symm) rfl (hl.trans hu)
  exact hc.trans (normalizedTensorTrianglePinched_principal_cochain A X Y c τ I hI
    hs1 hp1 haz hbt R hRset _ _ rfl rfl k hR hRs hRb hkR hJ hkJ)

end SerrePositivity.EInfinity.ComplexLimits
