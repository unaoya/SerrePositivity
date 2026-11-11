module
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexSubsetImageOrder
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceInSimplexVertexEquality
public import SerrePositivity.KST.SConstruction.NecklaceSimplexSubsetAt
public import SerrePositivity.KST.SConstruction.SimplexIntervalComposeRefinement
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklacePostcomposition

/-! # 元の単射な像部分集合 bead の augmentation
概要：元の部分集合上で単射な単調写像の後合成は、同じ像部分集合の元の bead。
方針：元の濃度等号の形移送と、全昇順頂点の像の一致で augmentation を判定する。
規約：元の全単体と両端を保持。使われ方：native HA の単射成分の自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet

/-- 元の部分集合上で単射な単調写像の後合成は、同じ元の像部分集合 augmentation。 -/
lemma necklaceInSimplexSubsetAt_image_inj {M N : ℕ}
    (α : Fin (M + 1) →o Fin (N + 1)) (I : Finset (Fin (M + 1)))
    (a b : Fin (M + 1)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hi : Set.InjOn α (I : Set (Fin (M + 1)))) (hJ : 2 ≤ (I.image α).card)
    (haJ : α a = (I.image α).min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (I.image α) hJ))
    (hbJ : α b = (I.image α).max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (I.image α) hJ)) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose (stdSimplex.map (SimplexCategory.Hom.mk α))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex.{u} a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)).obj
        (necklaceInSimplexSubsetAt I a b hI ha hb) =
      necklaceInSimplexSubsetAt (I.image α) (α a) (α b) hJ haJ hbJ := by
  have hc := (Finset.card_image_of_injOn hi).symm
  have he := congrArg (fun d => d - 1) hc
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInSimplex_eq_of_vertices (congrArg (necklaceBead.{u}) he)
  intro v
  change α (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder I hI v) =
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder (I.image α) hJ
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (eqToHom (congrArg (necklaceBead.{u}) he)) v)
  have hv : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (eqToHom (congrArg (necklaceBead.{u}) he)) v =
      Fin.cast (congrArg Nat.succ he) v := Fin.ext (necklaceBead_dimension_vertex he v)
  exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder_image_inj α I hI hi hJ v).symm.trans
    (congrArg (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetOrder (I.image α) hJ) hv.symm)

end SerrePositivity.KST.SConstruction
