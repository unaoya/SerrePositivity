module
public import SerrePositivity.KST.SConstruction.SimplexSubsetImageSerreFactor
public import SerrePositivity.KST.SConstruction.SerreCubeDegreeBounds
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeNormalizedComponent

/-! # 元の二点以上の非単射像を持つ高次 HA 成分の零性
概要：元の部分集合上非単射で像が二点以上なら、Λ 前合成の native HA 成分は実際に零。
方針：元の像部分集合を通る実 Serre 因子と、低次元 cube を通る最高生成元像の零性。
規約：像が一点の分岐は後続。使われ方：全退化作用素の高次零成分の自然性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の非単射な部分集合が二点以上の像を持つと、Λ 前合成の元の HA 成分は零。 -/
lemma cubicalLambdaNativeSimplexData_precompose_hom_zero_of_image_two {M N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D)
    (α : Fin (M + 1) →o Fin (N + 1)) (I : Finset (Fin (M + 1)))
    (a b : Fin (M + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (hk : k = 2 - (I.card : ℤ))
    (hi : ¬ Set.InjOn α (I : Set (Fin (M + 1)))) (hJ : 2 ≤ (I.image α).card) :
    (cubicalLambdaNativeSimplexData A (DGFunctor.comp
      (cubicalLambdaMap A (SSet.stdSimplex.map (SimplexCategory.Hom.mk α))) F)).hom
        I a b k hI ha hb hk = 0 := by
  let L := cubicalLambdaMap A (SSet.stdSimplex.map (SimplexCategory.Hom.mk α))
  let G := DGFunctor.comp L F
  have hc : (I.image α).card < I.card := lt_of_le_of_ne Finset.card_image_le
    (fun h => hi (Finset.card_image_iff.mp h))
  have hd : (I.image α).card - 2 < I.card - 2 := by omega
  have haJ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone
    (show IsLeast (I : Set (Fin (M + 1))) a from by rw [ha]; exact I.isLeast_min' _)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (I.image α) hJ)
  have hbJ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone
    (show IsGreatest (I : Set (Fin (M + 1))) b from by rw [hb]; exact I.isGreatest_max' _)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (I.image α) hJ)
  have hf := simplexSubsetLambdaCellAt_post_factor A α I a b hI ha hb hJ haJ hbJ
  have hchain : simplexSubsetLambdaCellAt A I a b hI ha hb ≫
      G.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) =
      simplexSubsetImageSerreFactor A α I hI hJ ≫
        (simplexSubsetLambdaCellAt A (I.image α) (α a) (α b) hJ haJ hbJ ≫
          F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α a)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b))) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α a)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b)))
        hf).trans (Category.assoc _ _ _))
  have htop : serreCubeTopCellImage A (homObject A D
      (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α a))) (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b)))) (I.card - 2)
      (simplexSubsetLambdaCellAt A I a b hI ha hb ≫
        G.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)) = 0 :=
    (congrArg (serreCubeTopCellImage A _ (I.card - 2)) hchain).trans
      (serreCubeTopCellImage_lower_dimension A hd _ _)
  have hn := cubicalLambdaNativeSimplexData_hom_normalized A G I a b k hI ha hb hk
  have hdeg : -((I.card - 2 : ℕ) : ℤ) = k := by omega
  exact hn.trans ((congrArg (fun x => eqToHom (congrArg (homObject A D
    (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α a))) (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b)))).X hdeg) x)
      htop).trans (map_zero _))

end SerrePositivity.KST.SConstruction
