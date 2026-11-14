module
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Chains.SimplexClosedIntervalSubsetOrder
public import SerrePositivity.KST.SConstruction.NecklaceSimplexSubsetAt
public import SerrePositivity.KST.SConstruction.SimplexIntervalComposeRefinement

/-! # 元の閉区間部分集合 bead と区間 bead の一致
概要：元の閉区間を部分集合として作った bead は、同じ両端の元の区間 bead と一致。
方針：元の全頂点の局所番号で終対象射を判定し、同じ augmentation を回収する。
規約：元の全高次単体と全頂点を保持。使われ方：native HA 逆構成の全 Hom 回収。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- 元の necklace の等号移送を持つ可換三角形は、同じ augmentation の対象等号を与える。 -/
lemma necklaceIn_eq_of_hom_eqToHom {K : SSet.{u}} {x y : K _⦋0⦌}
    {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y} (h : T.necklace = U.necklace) (f : T ⟶ U)
    (hf : f.necklaceHom = eqToHom h) : T = U := by
  obtain ⟨T, a, ha, hb⟩ := T
  obtain ⟨U, b, hc, hd⟩ := U
  change T = U at h
  subst U
  have hw := f.w
  rw [hf] at hw
  change (𝟙 T.down.carrier) ≫ b = a at hw
  rw [Category.id_comp] at hw
  cases hw
  rfl

/-- 元の閉区間部分集合の区間終対象への射は、同じ bead 長の等号移送そのもの。 -/
lemma necklaceClosedIntervalSubset_toInterval {N : ℕ} (a b : Fin (N + 1)) (hab : a ≤ b)
    (hI : 2 ≤ (Finset.Icc a b).card)
    (ha : a = (Finset.Icc a b).min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (Finset.Icc a b) hI))
    (hb : b = (Finset.Icc a b).max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (Finset.Icc a b) hI)) :
    (necklaceInToSimplexInterval a b hab
      (necklaceInSimplexSubsetAt.{u} (Finset.Icc a b) a b hI ha hb)).necklaceHom =
      eqToHom (congrArg (necklaceBead.{u})
        (show (Finset.Icc a b).card - 1 = b.val - a.val by
          rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClosedInterval_card a b hab]
          omega)) := by
  have he : (Finset.Icc a b).card - 1 = b.val - a.val := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClosedInterval_card a b hab]
    omega
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_injective
  funext v
  apply Fin.ext
  change (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder (Finset.Icc a b) hI v).val - a.val = _
  exact (congrArg (fun k => k - a.val)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_closedInterval_val a b hab hI v)).trans
      ((show a.val + v.val - a.val = v.val by omega).trans
        (necklaceBead_dimension_vertex he v).symm)

/-- 元の閉区間部分集合の augmentation は、同じ両端の元の区間 bead そのもの。 -/
lemma necklaceInSimplexSubsetAt_closedInterval {N : ℕ} (a b : Fin (N + 1)) (hab : a ≤ b)
    (hI : 2 ≤ (Finset.Icc a b).card)
    (ha : a = (Finset.Icc a b).min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (Finset.Icc a b) hI))
    (hb : b = (Finset.Icc a b).max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (Finset.Icc a b) hI)) :
    necklaceInSimplexSubsetAt.{u} (Finset.Icc a b) a b hI ha hb =
      necklaceInSimplexInterval a b hab :=
  necklaceIn_eq_of_hom_eqToHom
    (congrArg (necklaceBead.{u}) (show (Finset.Icc a b).card - 1 = b.val - a.val by
      rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClosedInterval_card a b hab]
      omega))
    (necklaceInToSimplexInterval a b hab
      (necklaceInSimplexSubsetAt (Finset.Icc a b) a b hI ha hb))
    (necklaceClosedIntervalSubset_toInterval a b hab hI ha hb)

end SerrePositivity.KST.SConstruction
