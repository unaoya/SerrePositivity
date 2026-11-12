module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseFullEquation
/-!
概要：逆構成の混合列は、両側の部分集合上で単射な二つの添字写像に自然である。
方針：パラメーター係数の像との比較と、元の部分単体ラベルの厳密な等式を使う。
規約：任意の線形成分族を扱い、端点を異種等号で保持する。
使われ方：逆データの単射自然性と全部分集合の HA 方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

private lemma nativeColumn_heq (p p' : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) (h : p = p') :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC p)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC p') := by
  cases h
  rfl

lemma dgCoherentBarInverseMixedColumn_reindex {a b n m : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (α : Fin (a + 1) →o Fin (n + 1))
    (β : Fin (b + 1) →o Fin (m + 1))
    (K : Finset (Fin (a + 1))) (L : Finset (Fin (b + 1)))
    (_hK : K.Nonempty) (hL : L.Nonempty)
    (hiK : Set.InjOn α (K : Set (Fin (a + 1))))
    (hiL : Set.InjOn β (L : Set (Fin (b + 1))))
    (r : ℕ) (hcK : K.card = r + 1) (q : ℤ) (hq : q = 1 - (L.card : ℤ)) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseMixedColumn R D F hMC N
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback β f) L q hL hq
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel (I.map (SimplexCategory.mkHom α).op s) K r hcK))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseMixedColumn R D F hMC N f (L.image β) q (hL.image β)
        (by rw [Finset.card_image_of_injOn hiL]; exact hq)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel s (K.image α) r
          (by rw [Finset.card_image_of_injOn hiK]; exact hcK))) := by
  have hLabel := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarSubsetLabel_map_of_injOn s α K hiK r hcK
  have hSource := congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F) hLabel
  have hNative := nativeColumn_heq R D F hMC _ _ hLabel
  have hPhi := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseParameterCoefficient_pullback_inj f β L q hL hq hiL
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseMixedColumn
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) (D := RightModule R D)
    hSource rfl rfl rfl rfl rfl
    (p := -(r : ℤ)) (q := q) (k := q - (r : ℤ))
    (p' := -(r : ℤ)) (q' := q) (k' := q - (r : ℤ))
    _ _ _ _ (heq_of_eq hPhi) hNative (by omega) (by omega)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
