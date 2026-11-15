module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ShuffleCutSum
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedEZHomotopy

/-!
概要：shuffle の後の AW と二因子の Moore 射影の合成を全テンソル上で計算する。
方針：標準包含で検出し、AW の有限和を対角成分に簡約する。
規約：既存の非正規化 shuffle・AW と元の射影を使う。
使われ方：HA 1.2.4、G10 の正規化した逆順合成の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- AW の各切断の後の正規化は、切断写像のテンソルの後に元の標準包含を置いたもの。 -/
theorem awSummand_mooreProjection
    (C D : SimplicialObject (ModuleCat.{u} ℤ)) (n : ℕ) (i : Fin (n + 1)) :
    alexanderWhitneySummand C D n i ≫
      (chainIntegerTensorMap (PInftyToNormalizedMooreComplex C)
        (PInftyToNormalizedMooreComplex D)).f n =
    integerTensorMap
      (C.map (awFront n i).op ≫ (PInftyToNormalizedMooreComplex C).f i)
      (D.map (awBack n i).op ≫ (PInftyToNormalizedMooreComplex D).f (n - i)) ≫
    ιMapBifunctor ((normalizedMooreComplex _).obj C) ((normalizedMooreComplex _).obj D)
      integerTensorBifunctor (.down ℕ) i (n - i) n (awDegrees n i) := by
  rw [alexanderWhitneySummand, Category.assoc, ι_chainIntegerTensorMap,
    ← Category.assoc, ← integerTensorMap_comp]
  rfl

/-- 全切断点の和の後でも、元の shuffle 成分は同じ次数の射影包含へ戻る。 -/
theorem shuffleBidegree_aw_projected
    (C D : SimplicialObject (ModuleCat.{u} ℤ)) (p n : ℕ) (hp : p ≤ n) :
    shuffleBidegree C D p (n - p) n (Nat.add_sub_of_le hp) ≫
      alexanderWhitneyApp C D n ≫
        (chainIntegerTensorMap (PInftyToNormalizedMooreComplex C)
          (PInftyToNormalizedMooreComplex D)).f n =
    integerTensorMap ((PInftyToNormalizedMooreComplex C).f p)
      ((PInftyToNormalizedMooreComplex D).f (n - p)) ≫
    ιMapBifunctor ((normalizedMooreComplex _).obj C) ((normalizedMooreComplex _).obj D)
      integerTensorBifunctor (.down ℕ) p (n - p) n (Nat.add_sub_of_le hp) := by
  rw [alexanderWhitneyApp, Preadditive.sum_comp, Preadditive.comp_sum]
  rw [Finset.sum_eq_single (⟨p, Nat.lt_succ_of_le hp⟩ : Fin (n + 1))]
  · rw [awSummand_mooreProjection, ← Category.assoc, shuffleBidegree_diagonal_projection C D p n hp]
  · intro i hi hne
    rw [awSummand_mooreProjection, ← Category.assoc,
      shuffleBidegree_offDiagonal_projection C D (Nat.add_sub_of_le hp) i
        (fun he => hne (Fin.ext he)), zero_comp]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

/-- 元の全テンソル上で shuffle→AW の後に射影すると、元の射影に一致する。 -/
theorem shuffle_aw_mooreProjection
    (C D : SimplicialObject (ModuleCat.{u} ℤ)) :
    shuffle C D ≫ alexanderWhitney C D ≫
      chainIntegerTensorMap (PInftyToNormalizedMooreComplex C)
        (PInftyToNormalizedMooreComplex D) =
    chainIntegerTensorMap (PInftyToNormalizedMooreComplex C)
      (PInftyToNormalizedMooreComplex D) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro p q h
  have hsum : p + q = n := h
  have hp : p ≤ n := by omega
  have hq : q = n - p := by omega
  subst q
  simp only [comp_f, ← Category.assoc]
  erw [ι_shuffleApp]
  rw [Category.assoc, ι_chainIntegerTensorMap]
  exact shuffleBidegree_aw_projected C D p n hp

/-- 途中の Moore 射影を既存のホモトピーで外し、逆順合成を恒等へ結ぶ。 -/
def normalizedShuffleAWHomotopy (C D : SimplicialObject (ModuleCat.{u} ℤ)) :
    Homotopy (normalizedShuffle C D ≫ normalizedAlexanderWhitney C D) (𝟙 _) := by
  let u := chainIntegerTensorMap (inclusionOfMooreComplexMap C)
    (inclusionOfMooreComplexMap D) ≫ shuffle C D
  let v := alexanderWhitney C D ≫ chainIntegerTensorMap
    (PInftyToNormalizedMooreComplex C) (PInftyToNormalizedMooreComplex D)
  let h := ((homotopyPInftyToId (simplicialIntegerTensor C D)).compLeft u).compRight v
  refine (Homotopy.ofEq ?_).trans (h.trans (Homotopy.ofEq ?_))
  · dsimp only [normalizedShuffle, normalizedAlexanderWhitney, u, v]
    simp only [Category.assoc]
    rw [← PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap,
      Category.assoc]
  · dsimp only [u, v]
    simp only [Category.comp_id, Category.assoc]
    rw [shuffle_aw_mooreProjection, ← chainIntegerTensorMap_comp]
    erw [(splitMonoInclusionOfMooreComplexMap C).id,
      (splitMonoInclusionOfMooreComplexMap D).id, chainIntegerTensorMap_id]

/-- 指定正規化 AW と shuffle による、両方向の実鎖ホモトピー同値。 -/
def normalizedSpecifiedEZEquiv (C D : SimplicialObject (ModuleCat.{u} ℤ)) :
    HomotopyEquiv ((normalizedMooreComplex _).obj (simplicialIntegerTensor C D))
      (chainIntegerTensor ((normalizedMooreComplex _).obj C) ((normalizedMooreComplex _).obj D)) where
  hom := normalizedAlexanderWhitney C D
  inv := normalizedShuffle C D
  homotopyHomInvId := (normalizedEZHomotopy C D).symm
  homotopyInvHomId := normalizedShuffleAWHomotopy C D

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
