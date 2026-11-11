module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinCoordinateCases
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataComponents
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedTerms
/-!
概要：join の HA 単体データは、純粋な左右の面と全混合成分により一意に決まる。
方針：成分添字を左右へ分割し、純粋な場合は既存の単射制限の成分比較を使う。
規約：方程式を課す前の単体データにも成立する。
使われ方：余錐空間の pinched Hom 比較の単射性と高次復元の一意性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {C : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]

private lemma hom_heq_of_image {l n : ℕ} (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n)
    (α : Fin (l + 1) →o Fin (n + 1)) (hα : Function.Injective α)
    (h : s.pullback α = t.pullback α) (K : Finset (Fin (l + 1)))
    (J : Finset (Fin (n + 1))) (hImg : K.image α = J)
    (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) : HEq (s.hom J a b k hJ ha hb hk) (t.hom J a b k hJ ha hb hk) := by
  have hcard : K.card = J.card :=
    (Finset.card_image_of_injective K hα).symm.trans (congrArg Finset.card hImg)
  have hK : 2 ≤ K.card := by omega
  have hA : α (K.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hK)) = a := by
    rw [ha]
    simpa only [hImg] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone (K.isLeast_min' _)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hK).image α)
  have hB : α (K.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hK)) = b := by
    rw [hb]
    simpa only [hImg] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone (K.isGreatest_max' _)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hK).image α)
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hom_heq_of_pullback_eq s t α α h K
    (K.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hK)) (K.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hK)) k hK rfl rfl
    (by rw [hcard]; exact hk) hα.injOn hα.injOn
  refine HEq.trans ?_ (hh.trans ?_)
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree s hImg.symm hA.symm hB.symm rfl
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree t hImg hA hB rfl

lemma dgCoherentBarJoinSimplexData_ext {n m : ℕ} (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C (n + m + 1))
    (hLeft : s.pullback (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m) =
      t.pullback (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m))
    (hRight : s.pullback (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m) =
      t.pullback (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m))
    (hMixed : ∀ (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1))),
      K.Nonempty → L.Nonempty →
      ∀ (a b : Fin (n + m + 1 + 1)) (k : ℤ)
        (hJ : 2 ≤ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).card)
        (ha : a = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
        (hb : b = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
        (hk : k = 2 - ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).card : ℤ)),
        HEq (s.hom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L) a b k hJ ha hb hk)
          (t.hom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L) a b k hJ ha hb hk)) : s = t := by
  have hObj : s.obj = t.obj := by
    funext i
    refine _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoin_cases (n := n) (m := m)
      (P := fun i => s.obj i = t.obj i) ?_ ?_ i
    · intro j
      exact congrArg (fun d : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n => d.obj j) hLeft
    · intro j
      exact congrArg (fun d : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C m => d.obj j) hRight
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext hObj
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise hObj
  intro J a b k hJ ha hb hk
  let K := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeftPart n m J
  let L := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRightPart n m J
  have hSet : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L = J := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_parts n m J
  by_cases hK : K.Nonempty
  · by_cases hL : L.Nonempty
    · have hJ' : 2 ≤ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).card := by simpa only [hSet] using hJ
      have ha' : a = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ') := by
        simpa only [hSet] using ha
      have hb' : b = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ') := by
        simpa only [hSet] using hb
      have hk' : k = 2 - ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).card : ℤ) := by
        simpa only [hSet] using hk
      refine HEq.trans ?_ ((hMixed K L hK hL a b k hJ' ha' hb' hk').trans ?_)
      · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree s hSet.symm rfl rfl rfl
      · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree t hSet rfl rfl rfl
    · have hLE : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
      have hImg : K.image (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m) = J := by
        simpa only [hLE, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset, Finset.image_empty, Finset.union_empty] using hSet
      exact hom_heq_of_image s t (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_injective n m) hLeft K J hImg a b k hJ ha hb hk
  · have hKE : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
    have hImg : L.image (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m) = J := by
      simpa only [hKE, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset, Finset.image_empty, Finset.empty_union] using hSet
    exact hom_heq_of_image s t (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight_injective n m) hRight L J hImg a b k hJ ha hb hk

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
