module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorUniversalSimplex
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexTensorAugmentation

/-!
# 元の正規化 frame の普遍 Hom 族の augmentation 像

概要：普遍族を元の augmentation で送ると、同じ零次数 augmentation の像の定数族となる。
方針：全 augmentation の自然性を同じ代表可能単体の式へ移す。
規約：零次数の像は明示し、恒等辺との同定は後続で検査する。
使われ方：正規化 frame 屋根の普遍評価方程式の projection 側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma normalizedTensorHomRepresentable_augmentation (X : Complex A) (n : SimplexCategory) :
    normalizedTensorHomRepresentable A X X n ((normalizedSimplexTensorAugmentation A X).app n) =
    SSet.const ((normalizedSimplexTensorAugmentation A X).app ⦋0⦌) := by
  apply SSet.yonedaEquiv.injective
  simp only [normalizedTensorHomRepresentable, Equiv.apply_symm_apply]
  change (normalizedSimplexTensorAugmentation A X).app n =
    (normalizedSimplexTensor A X).map (n.const ⦋0⦌ 0) ≫
      (normalizedSimplexTensorAugmentation A X).app ⦋0⦌
  have h := (normalizedSimplexTensorAugmentation A X).naturality (n.const ⦋0⦌ 0)
  change _ = (normalizedSimplexTensorAugmentation A X).app n ≫ 𝟙 X at h
  exact (h.trans (Category.comp_id _)).symm

lemma ulift_map_const {K L : SSet.{u}} (z : L _⦋0⦌) :
    SSet.uliftFunctor.{u + 1, u}.map (SSet.const (X := K) z) = SSet.const (ULift.up z) := rfl

def normalizedTensorAugmentationVertex (X : Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (Complex A) X X) _⦋0⦌ :=
  (normalizedTensorPinchedIso A X X).hom.app (Opposite.op ⦋0⦌)
    (ULift.up ((normalizedSimplexTensorAugmentation A X).app ⦋0⦌))

lemma normalizedTensorHomPinchedSimplex_augmentation (X : Complex A) (n : SimplexCategory) :
    normalizedTensorHomPinchedSimplex A X X n
      ((normalizedSimplexTensorAugmentation A X).app n) =
    SSet.const (normalizedTensorAugmentationVertex A X) := by
  dsimp only [normalizedTensorHomPinchedSimplex]
  rw [normalizedTensorHomRepresentable_augmentation, ulift_map_const, SSet.const_comp]
  rfl

lemma normalizedTensorUniversalSimplex_augmentation (X : Complex A) (n : SimplexCategory) :
    normalizedTensorUniversalSimplex A X n ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap
      (homPostcompose X ((normalizedSimplexTensorAugmentation A X).app n)) =
    SSet.const (normalizedTensorAugmentationVertex A X) := by
  rw [normalizedTensorUniversalSimplex_evaluation, normalizedTensorHomPinchedSimplex_augmentation]

end SerrePositivity.EInfinity.ComplexLimits
