module
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaAugmentation
public import SerrePositivity.KST.SConstruction.CubicalLambdaNativeNormalizedComponent
public import SerrePositivity.KST.SConstruction.SimplexHATopValueRecovery

/-! # 元の潰れる二点 HA 成分と dg 単位
概要：元の二点部分集合の両端が潰れると、Λ 前合成の native HA 成分は元の dg 単位。
方針：元の cell 増大・対角単位の実比較と、零次元の最高生成元像を使う。
規約：元の全二点部分集合・端点移送を保持。使われ方：全退化作用素の残る単位分岐。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

private lemma map_heq {C : Type u} [EnrichedCategory (Complex A) C]
    (F : EnrichedFunctor (Complex A) C D) {x x' y y' : C} (hx : x = x') (hy : y = y') :
    HEq (F.map x y) (F.map x' y') := by cases hx; cases hy; rfl

private lemma top_heq {K L : Complex A} (hK : K = L) (n : ℕ)
    (f : serreCubeComplex A n ⟶ K) (g : serreCubeComplex A n ⟶ L) (hfg : HEq f g) :
    HEq (serreCubeTopCellImage A K n f) (serreCubeTopCellImage A L n g) := by
  cases hK
  cases eq_of_heq hfg
  rfl

private lemma unit_top (Y : D) (n : ℕ) (hn : n = 0) :
    HEq (serreCubeTopCellImage A (homObject A D Y Y) n
      (serreCubeAugmentation A n ≫ eId (Complex A) Y)) (unitElement A Y).val := by
  subst n
  apply heq_of_eq
  change (eId (Complex A) Y).f 0 (serreCubeOrientedTopCell A 0) = _
  rw [serreCubeOrientedTopCell_zero]
  change (cycleFromUnit _ (𝟙 _ ≫ eId (Complex A) Y)).val = _
  rw [Category.id_comp]
  rfl

/-- 元の二点部分集合の両端が同じ像頂点なら、Λ 前合成の成分は元の dg 単位。 -/
lemma cubicalLambdaNativeSimplexData_precompose_hom_pair_unit_heq {M N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D)
    (α : Fin (M + 1) →o Fin (N + 1)) (I : Finset (Fin (M + 1)))
    (a b : Fin (M + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (hk : k = 2 - (I.card : ℤ))
    (hab : α a = α b) (hc : I.card = 2) :
    HEq ((cubicalLambdaNativeSimplexData A (DGFunctor.comp
      (cubicalLambdaMap A (SSet.stdSimplex.map (SimplexCategory.Hom.mk α))) F)).hom
        I a b k hI ha hb hk) (unitElement A (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b)))).val := by
  let L := cubicalLambdaMap A (SSet.stdSimplex.map (SimplexCategory.Hom.mk α))
  let G := DGFunctor.comp L F
  let n := I.card - 2
  have hcell := simplexSubsetLambdaCellAt_post_diagonal_heq A α I a b hI ha hb hab
  have hmap := map_heq A F (congrArg (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex.{u}) hab)
    (rfl : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex.{u} (α b) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b))
  have hK := congrArg (fun x => homObject A D
    (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex x)) (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b)))) hab
  have hcomp := heq_comp (rfl : serreCubeComplex A n = serreCubeComplex A n)
    (congrArg (fun x => homObject A (CubicalLambda A (Δ[N] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex x) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b))) hab) hK hcell hmap
  have hu : (serreCubeAugmentation A n ≫
      eId (C := CubicalLambda A (Δ[N] : SSet.{u})) (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b))) ≫
      F.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b)) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b)) =
      serreCubeAugmentation A n ≫ eId (Complex A) (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b))) :=
    (Category.assoc _ _ _).trans (congrArg (fun f => serreCubeAugmentation A n ≫ f)
      (F.map_id (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b))))
  have hall : HEq (simplexSubsetLambdaCellAt A I a b hI ha hb ≫
      G.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))
      (serreCubeAugmentation A n ≫ eId (Complex A) (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b)))) :=
    (heq_of_eq (Category.assoc _ _ _).symm).trans (hcomp.trans (heq_of_eq hu))
  have htop := top_heq A hK n _ _ hall
  have hn := cubicalLambdaNativeSimplexData_hom_normalized A G I a b k hI ha hb hk
  have hdeg : -(n : ℤ) = k := by dsimp [n]; omega
  exact ((heq_of_eq hn).trans (complexElement_degree_cast_heq A _ hdeg _)).trans
    (htop.trans (unit_top A (F.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b))) n (by dsimp [n]; omega)))

/-- 元の潰れる二点部分集合で、Λ 前合成は native HA 引き戻しの元の単位分岐を回収。 -/
lemma cubicalLambdaNativeSimplexData_precompose_hom_of_collapsed_pair {M N : ℕ}
    (F : DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D)
    (α : Fin (M + 1) →o Fin (N + 1)) (I : Finset (Fin (M + 1)))
    (a b : Fin (M + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (hk : k = 2 - (I.card : ℤ))
    (hi : ¬ Set.InjOn α (I : Set (Fin (M + 1)))) (hc : I.card = 2) :
    (cubicalLambdaNativeSimplexData A (DGFunctor.comp
      (cubicalLambdaMap A (SSet.stdSimplex.map (SimplexCategory.Hom.mk α))) F)).hom
        I a b k hI ha hb hk =
      ((cubicalLambdaNativeSimplexData A F).pullback α).hom I a b k hI ha hb hk := by
  have hab := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.collapse_two hi hc
    (show IsLeast (I : Set (Fin (M + 1))) a from by rw [ha]; exact I.isLeast_min' _)
    (show IsGreatest (I : Set (Fin (M + 1))) b from by rw [hb]; exact I.isGreatest_max' _)
  exact eq_of_heq ((cubicalLambdaNativeSimplexData_precompose_hom_pair_unit_heq A F α I a b k
    hI ha hb hk hab hc).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_collapsed_pair
      (cubicalLambdaNativeSimplexData A F) α I a b k hI ha hb hk hi hc).symm)

end SerrePositivity.KST.SConstruction
