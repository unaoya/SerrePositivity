module
public import SerrePositivity.KST.Fibration.WeakStringOctahedronMiddle
public import SerrePositivity.KST.Fibration.WeakStringCofiberRealization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LocalizedPairEquality
public import SerrePositivity.KST.SConstruction.MultiRealizationFunctorIso

/-! # 元の三辺の共通 cofiber 関手の全正有限反復加法性

八面体比較列の K-1 加法性を、固定 K-1/K-2 の関手同型不変性により元の三辺へ移す。
結果の射対と加法射の合成は、全ての面・退化と整合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の実二単体の長辺の cofiber 射は、二つの短辺の cofiber 射の加法射である。 -/
theorem weakStringTriangleMultiAddition {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (β : ⦋2⦌ ⟶ n) (r : ℕ) :
    AnodyneHomotopy.anodyneQ.map
      (weakStringCofiberMultiMap q (SimplexCategory.δ (1 : Fin 3) ≫ β) (r + 1)) =
        AnodyneHomotopy.anodyneQ.map (weakStringCofiberMultiPair q
          (SimplexCategory.δ (2 : Fin 3) ≫ β) (SimplexCategory.δ (0 : Fin 3) ≫ β) (r + 1)) ≫
            kernelMultiAddition q r := by
  have hm := multiRealization_map_positive_localized_eq_of_functorIso r
    (weakStringOctahedronMiddleExact_comparison q β)
  have ht := multiRealization_map_positive_localized_eq_of_functorIso r
    (weakStringOctahedronTargetExact_comparison q β)
  change AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor (r + 1)).map
    (weakStringKernelCofiber q (SimplexCategory.δ (1 : Fin 3) ≫ β))) = _
  rw [← hm, weakStringOctahedronMultiAddition]
  exact congrArg (· ≫ kernelMultiAddition q r)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pair_right_eq_of_anodyneQ_eq
      ((multiRealizationFunctor (r + 1)).map
        (weakStringKernelCofiber q (SimplexCategory.δ (2 : Fin 3) ≫ β))) ht)

/-- 元の三辺の加法性の右辺は、全ての列の面・退化の制限と整合する。 -/
lemma weakStringTriangleMultiAddition_reindex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {m n : SimplexCategory} (θ : m ⟶ n) (β : ⦋2⦌ ⟶ m) (r : ℕ) :
    AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor (r + 1)).map
      (weakStringExactMap q θ)) ≫
        (AnodyneHomotopy.anodyneQ.map (weakStringCofiberMultiPair q
          (SimplexCategory.δ (2 : Fin 3) ≫ β) (SimplexCategory.δ (0 : Fin 3) ≫ β) (r + 1)) ≫
            kernelMultiAddition q r) =
      AnodyneHomotopy.anodyneQ.map (weakStringCofiberMultiPair q
        (SimplexCategory.δ (2 : Fin 3) ≫ (β ≫ θ))
        (SimplexCategory.δ (0 : Fin 3) ≫ (β ≫ θ)) (r + 1)) ≫ kernelMultiAddition q r := by
  have he := weakStringCofiberMultiPair_reindex q θ
    (SimplexCategory.δ (2 : Fin 3) ≫ β) (SimplexCategory.δ (0 : Fin 3) ≫ β) (r + 1)
  simp only [Category.assoc] at he
  rw [← Category.assoc, ← Functor.map_comp, he]

end SerrePositivity.KST.Fibration
