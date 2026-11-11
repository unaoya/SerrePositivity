module
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaImageCell
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeNormalizedComponent
public import SerrePositivity.KST.SConstruction.SimplexHATopValueRecovery

/-! # 元の単体作用素の単射部分集合上の native HA 成分
概要：元の標準単体写像の Λ 前合成は、部分集合上単射なら元の HA 引き戻し成分を回収。
方針：元の像 cell 比較と同じ HA 向き最高生成元像を、同じ指定次数へ移す。
規約：元の全単射部分集合・端点・次数を保持。使われ方：全単体作用素の厳密自然性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

private lemma top_heq (K : Complex A) {m n : ℕ} (h : m = n)
    (f : serreCubeComplex A m ⟶ K) (g : serreCubeComplex A n ⟶ K) (hfg : HEq f g) :
    HEq (serreCubeTopCellImage A K m f) (serreCubeTopCellImage A K n g) := by
  cases h
  cases eq_of_heq hfg
  rfl

/-- 元の部分集合上単射な標準単体写像の Λ 前合成は、元の HA 引き戻し成分を回収。 -/
lemma cubicalLambdaNativeSimplexData_precompose_hom_of_inj {M N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D)
    (α : Fin (M + 1) →o Fin (N + 1)) (I : Finset (Fin (M + 1)))
    (a b : Fin (M + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (hk : k = 2 - (I.card : ℤ))
    (hi : Set.InjOn α (I : Set (Fin (M + 1)))) :
    (cubicalLambdaNativeSimplexData A (DGFunctor.comp
      (cubicalLambdaMap A (SSet.stdSimplex.map (SimplexCategory.Hom.mk α))) F)).hom
        I a b k hI ha hb hk =
      ((cubicalLambdaNativeSimplexData A F).pullback α).hom I a b k hI ha hb hk := by
  let L := cubicalLambdaMap A (SSet.stdSimplex.map (SimplexCategory.Hom.mk α))
  let G := DGFunctor.comp L F
  have hJ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hi hI
  have haJ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone
    (show IsLeast (I : Set (Fin (M + 1))) a from by rw [ha]; exact I.isLeast_min' _)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (I.image α) hJ)
  have hbJ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone
    (show IsGreatest (I : Set (Fin (M + 1))) b from by rw [hb]; exact I.isGreatest_max' _)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (I.image α) hJ)
  have hkJ : k = 2 - ((I.image α).card : ℤ) := by
    rw [Finset.card_image_of_injOn hi]
    exact hk
  have hdim : I.card - 2 = (I.image α).card - 2 :=
    congrArg (fun d => d - 2) (Finset.card_image_of_injOn hi).symm
  have hcell := simplexSubsetLambdaCellAt_image_inj_heq A α I a b hI ha hb hi hJ haJ hbJ
  have hcomp := heq_comp (congrArg (serreCubeComplex A) hdim) rfl rfl hcell
    (HEq.rfl : HEq (F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α a)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b)))
      (F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α a)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b))))
  have hall : HEq (simplexSubsetLambdaCellAt A I a b hI ha hb ≫
      G.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))
      (simplexSubsetLambdaCellAt A (I.image α) (α a) (α b) hJ haJ hbJ ≫
        F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α a)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b))) :=
    (heq_of_eq (Category.assoc _ _ _).symm).trans hcomp
  have htop := top_heq A (homObject A D
    (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α a))) (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b)))) hdim _ _ hall
  have hn := cubicalLambdaNativeSimplexData_hom_normalized A G I a b k hI ha hb hk
  have hm := cubicalLambdaNativeSimplexData_hom_normalized A F (I.image α) (α a) (α b) k
    hJ haJ hbJ hkJ
  have hki : -((I.card - 2 : ℕ) : ℤ) = k := by omega
  have hkj : -(((I.image α).card - 2 : ℕ) : ℤ) = k := by omega
  have he := ((heq_of_eq hn).trans (complexElement_degree_cast_heq A _ hki _)).trans
    (htop.trans ((heq_of_eq hm).trans (complexElement_degree_cast_heq A _ hkj _)).symm)
  exact (eq_of_heq he).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj (cubicalLambdaNativeSimplexData A F)
      α I a b k hI ha hb hk hi).symm

end SerrePositivity.KST.SConstruction
