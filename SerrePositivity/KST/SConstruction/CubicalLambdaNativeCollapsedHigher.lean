module
public import SerrePositivity.KST.SConstruction.SimplexDiagonalLambdaDegree
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeNoninjectiveImage

/-! # 元の潰れた高次 HA 成分の全分岐の実零性
概要：両端が潰れる高次成分も実際に零となり、全非単射の高次成分を同じ零式へ束ねる。
方針：元の対角 Hom の次数消滅と、二点以上の像を通る実 Serre 因子を使う。
規約：元の全像濃度と次数を保持。使われ方：全退化作用素の高次成分の自然性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の二点でない部分集合の両端が同じ像頂点なら、Λ 前合成の HA 成分は零。 -/
lemma cubicalLambdaNativeSimplexData_precompose_hom_zero_of_endpoints {M N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D)
    (α : Fin (M + 1) →o Fin (N + 1)) (I : Finset (Fin (M + 1)))
    (a b : Fin (M + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (hk : k = 2 - (I.card : ℤ))
    (hab : α a = α b) (hc : I.card ≠ 2) :
    (cubicalLambdaNativeSimplexData A (DGFunctor.comp
      (cubicalLambdaMap A (SSet.stdSimplex.map (SimplexCategory.Hom.mk α))) F)).hom
        I a b k hI ha hb hk = 0 := by
  have hk0 : k ≠ 0 := by omega
  subst a b k
  let L := cubicalLambdaMap A (SSet.stdSimplex.map (SimplexCategory.Hom.mk α))
  have hz : IsZero ((homObject A (CubicalLambda A (Δ[N] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))))).X
      (2 - (I.card : ℤ))) := by
    rw [hab]
    exact simplexDiagonalLambdaHom_X_isZero A _ _ hk0
  have hs := ModuleCat.subsingleton_of_isZero hz
  have hx : (L.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)))).f (2 - (I.card : ℤ))
      (simplexSubsetLambdaGenerator A I hI) = 0 :=
    hs.elim _ _
  exact (congrArg (fun x => (F.map
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α (I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))))
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α (I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))))).f (2 - (I.card : ℤ)) x)
      hx).trans (map_zero _)

/-- 元の任意の非単射な高次部分集合で、Λ 前合成は native HA 引き戻しの零成分を回収。 -/
lemma cubicalLambdaNativeSimplexData_precompose_hom_of_not_inj {M N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D)
    (α : Fin (M + 1) →o Fin (N + 1)) (I : Finset (Fin (M + 1)))
    (a b : Fin (M + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (hk : k = 2 - (I.card : ℤ))
    (hi : ¬ Set.InjOn α (I : Set (Fin (M + 1)))) (hc : I.card ≠ 2) :
    (cubicalLambdaNativeSimplexData A (DGFunctor.comp
      (cubicalLambdaMap A (SSet.stdSimplex.map (SimplexCategory.Hom.mk α))) F)).hom
        I a b k hI ha hb hk =
      ((cubicalLambdaNativeSimplexData A F).pullback α).hom I a b k hI ha hb hk := by
  have hz : (cubicalLambdaNativeSimplexData A (DGFunctor.comp
      (cubicalLambdaMap A (SSet.stdSimplex.map (SimplexCategory.Hom.mk α))) F)).hom
      I a b k hI ha hb hk = 0 := by
    by_cases hJ : 2 ≤ (I.image α).card
    · exact cubicalLambdaNativeSimplexData_precompose_hom_zero_of_image_two A F α I a b k
        hI ha hb hk hi hJ
    · have hab : α a = α b := (Finset.card_le_one.mp (by omega)) _
        (Finset.mem_image.mpr ⟨a, ha.symm ▸ Finset.min'_mem _ _, rfl⟩) _
        (Finset.mem_image.mpr ⟨b, hb.symm ▸ Finset.max'_mem _ _, rfl⟩)
      exact cubicalLambdaNativeSimplexData_precompose_hom_zero_of_endpoints A F α I a b k
        hI ha hb hk hab hc
  exact hz.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj
    (cubicalLambdaNativeSimplexData A F) α I a b k hI ha hb hk hi hc).symm

end SerrePositivity.KST.SConstruction
