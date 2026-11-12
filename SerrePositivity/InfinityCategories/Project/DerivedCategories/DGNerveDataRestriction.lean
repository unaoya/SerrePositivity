module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DataComponents
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedTerms
/-!
概要：全ての低次数への単射制限の一致から、真の部分集合の同じ Hom 成分の一致を回収する。
方針：指定した有限集合を昇順で標準単体へ移し、その同じ像の成分を比較する。
規約：元の生のデータに HA を仮定しない。使われ方：全次元候補の自然性の帰納法。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 全ての低次数への単射制限が一致する生のデータは、真の部分集合の同じ成分で一致する。 -/
lemma dgNerveData_hom_heq_of_smaller_restrictions {m : ℕ} (X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D m)
    (hres : ∀ (r : ℕ), r < m → ∀ (γ : Fin (r + 1) →o Fin (m + 1)),
      Function.Injective γ → X.pullback γ = Y.pullback γ)
    (I : Finset (Fin (m + 1))) (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hproper : I.card < m + 1) :
    HEq (X.hom I a b k hI ha hb hk) (Y.hom I a b k hI ha hb hk) := by
  let r := I.card - 1
  have hcard : I.card = r + 1 := by omega
  have hr : r < m := by omega
  let e := I.orderEmbOfFin hcard
  let γ : Fin (r + 1) →o Fin (m + 1) := e.toOrderHom
  let E : Finset (Fin (r + 1)) := Finset.univ
  have hE : 2 ≤ E.card := by
    simpa only [E, Finset.card_univ, Fintype.card_fin, ← hcard] using hI
  have hγI : E.image γ = I := I.image_orderEmbOfFin_univ hcard
  let a₀ := E.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE)
  let b₀ := E.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE)
  have hγa : γ a₀ = a := by
    rw [ha]
    simpa only [hγI] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min γ.monotone
      (E.isLeast_min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE)) (Finset.Nonempty.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE) γ)
  have hγb : γ b₀ = b := by
    rw [hb]
    simpa only [hγI] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max γ.monotone
      (E.isGreatest_max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE)) (Finset.Nonempty.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hE) γ)
  have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hom_heq_of_pullback_eq X Y γ γ (hres r hr γ e.injective)
    E a₀ b₀ k hE rfl rfl
    (by simpa only [E, Finset.card_univ, Fintype.card_fin, ← hcard] using hk)
    e.injective.injOn e.injective.injOn
  cases hγa
  cases hγb
  simpa only [hγI] using H
end SerrePositivity.InfinityCategories.Project.DerivedCategories
