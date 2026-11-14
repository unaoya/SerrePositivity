module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.IdentityLaxDiagonal

public import SerrePositivity.KST.LocalizingInvariants.ArrowStableExact
public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceExact
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConstantFunctor

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.IdentityLax

variable (A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})

def diagonal : A.obj ⟶ (laxCategory (𝟙 A) (𝟙 A)).obj :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (Δ[1] : SSet.{u}) A.obj ≫ _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse A.obj

lemma diagonal_fst : diagonal A ≫ (laxFst (𝟙 A) (𝟙 A)).hom = 𝟙 A.obj := by
  change diagonal A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst (𝟙 A.obj) (𝟙 A.obj) = _
  rw [diagonal, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse_fst, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.constant_evaluation]

lemma diagonal_snd : diagonal A ≫ (laxSnd (𝟙 A) (𝟙 A)).hom = 𝟙 A.obj := by
  change diagonal A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd (𝟙 A.obj) (𝟙 A.obj) = _
  rw [diagonal, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse_snd, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Lax.constant_evaluation]

instance diagonal_isExact : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (diagonal A) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (diagonal A ≫ (laxFst (𝟙 A) (𝟙 A)).hom) := by
    rw [diagonal_fst]; infer_instance
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (diagonal A ≫ (laxSnd (𝟙 A) (𝟙 A)).hom) := by
    rw [diagonal_snd]; infer_instance
  exact LaxInclusion.exact_of_components (𝟙 A) (𝟙 A) _

def exactDiagonal : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory (𝟙 A) (𝟙 A)) := ⟨diagonal A, inferInstance⟩

lemma difference_diagonal_zero (x : A.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((diagonal A ≫ laxDifference (𝟙 A) (𝟙 A)).app (Opposite.op ⦋0⦌) x) := by
  apply (laxDifference_zero_iff (𝟙 A) (𝟙 A) _).2
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex ((diagonal A ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 A.obj) (𝟙 A.obj)).app (Opposite.op ⦋0⦌) x)
  rw [diagonal, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Quasicategory.arrowLaxInverse_arrow, Category.comp_id,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isEquivalencePathVertex_const x

end SerrePositivity.KST.LocalizingInvariants.IdentityLax
