module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorDoubleConeTailFront

/-!
概要：通常終端付き列の全終端 cochain は、元の augmentation 自身の同じ閉成分である。
方針：元の終端射を回収し、対象と chain map の輸送を保って閉 cochain へ移す。
規約：全次数・全有限集合の成分。使われ方：実二重 cone の終端部分との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (X Y : Complex A)

private lemma closedHom_heq {P Q P' Q' : Complex A} (hP : P = P') (hQ : Q = Q')
    (f : P ⟶ Q) (g : P' ⟶ Q') (hf : HEq f g) (k : ℤ) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed A).map f) k)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed A).map g) k) := by
  cases hP
  cases hQ
  cases eq_of_heq hf
  rfl

lemma normalizedTensorElementAugmentedColumn_hom_last {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n)
    (I : Finset (Fin (n + 2))) (a b : Fin (n + 2)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (hbl : b = Fin.last (n + 1)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (normalizedTensorElementAugmentedColumn A X Y c ⋙
      complexToClosed A)).hom I a b k hI ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed A).map ((normalizedTensorElementAugmentation A X Y).app
        (c.obj ((Fin.last n).predAboveOrderHom a)))) k) := by
  have han : a ≠ Fin.last (n + 1) := by rw [ha]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_ne_last I hI
  have ha' : a = ((Fin.last n).predAboveOrderHom a).castSucc :=
    (complexRightConeIndex_recover a han).symm
  have hab : a ≤ b := by rw [ha, hb]; exact I.min'_le _ (I.max'_mem _)
  have hx : (normalizedTensorElementAugmentedColumn A X Y c).obj a =
      (normalizedTensorElementDiagram A X Y).obj (c.obj ((Fin.last n).predAboveOrderHom a)) := by
    exact (congrArg (normalizedTensorElementAugmentedColumn A X Y c).obj ha').trans
      (normalizedTensorElementAugmentedColumn_obj_castSucc A X Y c _)
  have hy : (normalizedTensorElementAugmentedColumn A X Y c).obj b = X := by
    rw [hbl, normalizedTensorElementAugmentedColumn_obj_last]
  have ht : ∀ (a b : Fin (n + 2)) (i : Fin (n + 1)) (ha : a = i.castSucc)
      (hb : b = Fin.last (n + 1)) (h : a ≤ b),
      HEq ((normalizedTensorElementAugmentedColumn A X Y c).map (homOfLE h))
        ((normalizedTensorElementAugmentation A X Y).app (c.obj i)) := by
    intro a b i ha hb h
    subst a
    subst b
    exact normalizedTensorElementAugmentedColumn_map_cast_last A X Y c i
  change HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed A).map
    ((normalizedTensorElementAugmentedColumn A X Y c).map (homOfLE hab))) k) _
  exact closedHom_heq A hx hy _ _ (ht a b _ ha' hbl hab) k

end SerrePositivity.EInfinity.ComplexLimits
