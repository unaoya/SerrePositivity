module
public import SerrePositivity.InfinityCategories.Stable.Lax.IdentityLaxDiagonal

public import SerrePositivity.KST.LocalizingInvariants.ArrowStableExact
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceExact
public import SerrePositivity.InfinityCategories.F1B.Adjunction.ConstantFunctor

/-!
概要：恒等二関手の lax pullback に恒等矢印の実対角を入れ、その差が全値を零化する。
方針：定値矢印族と矢印圏からの厳密逆を合成し、元の両射影と核の条件を計算する。
規約：頂点だけの対角に弱めない。使われ方：不変量による suspension の整数 π の負号。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.IdentityLax

variable (A : StableCategory.{u})

def diagonal : A.obj ⟶ (laxCategory (𝟙 A) (𝟙 A)).obj :=
  constantFunctorMap (Δ[1] : SSet.{u}) A.obj ≫ arrowLaxInverse A.obj

lemma diagonal_fst : diagonal A ≫ (laxFst (𝟙 A) (𝟙 A)).hom = 𝟙 A.obj := by
  change diagonal A ≫ F2.laxPullbackFst (𝟙 A.obj) (𝟙 A.obj) = _
  rw [diagonal, Category.assoc, arrowLaxInverse_fst, constant_evaluation]

lemma diagonal_snd : diagonal A ≫ (laxSnd (𝟙 A) (𝟙 A)).hom = 𝟙 A.obj := by
  change diagonal A ≫ F2.laxPullbackSnd (𝟙 A.obj) (𝟙 A.obj) = _
  rw [diagonal, Category.assoc, arrowLaxInverse_snd, constant_evaluation]

instance diagonal_isExact : IsExactFunctor (diagonal A) := by
  have : IsExactFunctor (diagonal A ≫ (laxFst (𝟙 A) (𝟙 A)).hom) := by
    rw [diagonal_fst]; infer_instance
  have : IsExactFunctor (diagonal A ≫ (laxSnd (𝟙 A) (𝟙 A)).hom) := by
    rw [diagonal_snd]; infer_instance
  exact LaxInclusion.exact_of_components (𝟙 A) (𝟙 A) _

def exactDiagonal : ExactMap A (laxCategory (𝟙 A) (𝟙 A)) := ⟨diagonal A, inferInstance⟩

lemma difference_diagonal_zero (x : A.obj _⦋0⦌) :
    IsZeroVertex ((diagonal A ≫ laxDifference (𝟙 A) (𝟙 A)).app (Opposite.op ⦋0⦌) x) := by
  apply (laxDifference_zero_iff (𝟙 A) (𝟙 A) _).2
  change IsEquivalencePathVertex ((diagonal A ≫
    F2.laxPullbackArrow (𝟙 A.obj) (𝟙 A.obj)).app (Opposite.op ⦋0⦌) x)
  rw [diagonal, Category.assoc, arrowLaxInverse_arrow, Category.comp_id,
    constantFunctorMap_vertex]
  exact isEquivalencePathVertex_const x

end SerrePositivity.KST.LocalizingInvariants.IdentityLax
