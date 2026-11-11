module
public import SerrePositivity.KST.SConstruction.NecklaceSimplexSubsetImageFactor
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaNecklaceCell
public import SerrePositivity.KST.SConstruction.NecklaceLambdaCellPostcomposition

/-! # 元の像部分集合を通る標準次元の実 Serre 因子
概要：単射性なしの像 necklace 因子を鎖化し、元の部分集合と像の濃度次元で読む。
方針：元の次元移送と necklace 表示関係・後合成自然性を照合する。
規約：像が二点以上の分岐と元の実鎖射を保持。使われ方：高次退化の次数による零性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

private lemma cancel_transport {X Y Z W R : Complex A} (e : X ⟶ Y) (f : Y ⟶ Z)
    (h : Z = W) (g : Z ⟶ R) :
    (e ≫ f ≫ eqToHom h) ≫ (eqToHom h.symm ≫ g) = e ≫ f ≫ g := by
  cases h
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp, Category.assoc]

/-- 元の像部分集合を通る、同じ濃度次元間の元の実 Serre 鎖射。 -/
def simplexSubsetImageSerreFactor {M N : ℕ} (α : Fin (M + 1) →o Fin (N + 1))
    (I : Finset (Fin (M + 1))) (hI : 2 ≤ I.card) (hJ : 2 ≤ (I.image α).card) :
    serreCubeComplex A (I.card - 2) ⟶ serreCubeComplex A ((I.image α).card - 2) :=
  eqToHom (congrArg (serreCubeComplex A) (necklaceInSimplexSubset_dimension.{u} I hI).symm) ≫
    (serreConcreteCubeComplexFunctor A).map
      (necklaceConcreteCubeMap (necklaceSimplexSubsetImageFactor.{u} α I hI hJ)) ≫
        eqToHom (congrArg (serreCubeComplex A) (necklaceInSimplexSubset_dimension.{u} _ hJ))

/-- 元の入力の Λ 作用は、同じ元の像部分集合の実 Serre 因子と cell を通る。 -/
lemma simplexSubsetLambdaCellAt_post_factor {M N : ℕ}
    (α : Fin (M + 1) →o Fin (N + 1)) (I : Finset (Fin (M + 1)))
    (a b : Fin (M + 1)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (hJ : 2 ≤ (I.image α).card)
    (haJ : α a = (I.image α).min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (I.image α) hJ))
    (hbJ : α b = (I.image α).max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty (I.image α) hJ)) :
    simplexSubsetLambdaCellAt A I a b hI ha hb ≫
      (cubicalLambdaMap A (SSet.stdSimplex.map (SimplexCategory.Hom.mk α))).map
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) =
      simplexSubsetImageSerreFactor A α I hI hJ ≫
        simplexSubsetLambdaCellAt A (I.image α) (α a) (α b) hJ haJ hbJ := by
  let φ := SSet.stdSimplex.map (SimplexCategory.Hom.mk α)
  let T := necklaceInSimplexSubsetAt.{u} I a b hI ha hb
  let U := necklaceInSimplexSubsetAt.{u} (I.image α) (α a) (α b) hJ haJ hbJ
  have hr := necklaceLambdaCell_relation A
    (necklaceInSimplexSubsetImageFactor.{u} α I a b hI ha hb hJ haJ hbJ)
  have hp := necklaceLambdaCell_post A φ T
  have hL := congrArg (fun f => f ≫ (cubicalLambdaMap A φ).map
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))
      (simplexSubsetLambdaCellAt_necklace A I a b hI ha hb)
  have hR : simplexSubsetImageSerreFactor A α I hI hJ ≫
      simplexSubsetLambdaCellAt A (I.image α) (α a) (α b) hJ haJ hbJ =
      eqToHom (congrArg (serreCubeComplex A) (necklaceInSimplexSubset_dimension.{u} I hI).symm) ≫
        (serreConcreteCubeComplexFunctor A).map
          (necklaceConcreteCubeMap (necklaceSimplexSubsetImageFactor.{u} α I hI hJ)) ≫
            necklaceLambdaCell A U := by
    rw [simplexSubsetLambdaCellAt_necklace]
    exact cancel_transport A _ _
      (congrArg (serreCubeComplex A) (necklaceInSimplexSubset_dimension.{u} _ hJ))
      (necklaceLambdaCell A U)
  exact hL.trans ((Category.assoc _ _ _).trans
    ((congrArg (fun f => eqToHom (congrArg (serreCubeComplex A)
      (necklaceInSimplexSubset_dimension.{u} I hI).symm) ≫ f) (hp.trans hr.symm)).trans hR.symm))

end SerrePositivity.KST.SConstruction
