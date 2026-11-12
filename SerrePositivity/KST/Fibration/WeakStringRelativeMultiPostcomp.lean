module
public import SerrePositivity.KST.Fibration.WeakStringRelativeCorePostcomp
public import SerrePositivity.KST.Fibration.WeakStringRelativeMultiRealization

/-! # 全長の有限加法性と同じ反復実現模型で元の包含側の四角形を保つ -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の包含側の完全関手を、同じ全反復実現の全 W 列方向へ送る。 -/
def weakStringMultiPostcomp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    weakStringMultiRealization (f ≫ q : A ⟶ C) r ⟶ weakStringMultiRealization q r :=
  Functor.whiskerRight (weakStringStablePostcomp f q) (multiRealizationFunctor r)

/-- 単回実現の座標同型も、元の包含側の完全関手と全 W 列の段で厳密に可換。 -/
lemma weakStringCoreSingleRealizationIso_postcomp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    Functor.whiskerRight (weakStringStablePostcomp f q) coreSRealizationFunctor ≫
      (weakStringCoreSingleRealizationIso q).hom =
        (weakStringCoreSingleRealizationIso (f ≫ q : A ⟶ C)).hom ≫
          weakStringMultiPostcomp f q 1 := by
  apply NatTrans.ext
  funext n
  exact coreSingleRealizationIso_naturality (weakStringPostExact f q n.unop)

/-- 元の相対 S から全長の加法性で使う実現への比較は、元の包含側の完全関手を保つ。 -/
theorem relativeSWeakStringMultiComparison_postcomp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    simplicialDiagonalFunctor.map (relativeSimplicialFunctorMap f q.hom) ≫
      relativeSWeakStringMultiComparison q =
        relativeSWeakStringMultiComparison (f ≫ q : A ⟶ C) ≫
          simplicialDiagonalFunctor.map (weakStringMultiPostcomp f q 1) := by
  unfold relativeSWeakStringMultiComparison
  rw [← Category.assoc, relativeSWeakStringCoreComparison_postcomp, Category.assoc,
    ← Functor.map_comp, weakStringCoreSingleRealizationIso_postcomp, Functor.map_comp,
    ← Category.assoc]

/-- 元の相対 S の核側の写像を、有限加法性と同じ実現模型で運ぶ可換四角形。 -/
theorem relativeSWeakStringMultiComparison_square {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    CommSq (relativeSWeakStringMultiComparison (f ≫ q : A ⟶ C))
      (simplicialDiagonalFunctor.map (relativeSimplicialFunctorMap f q.hom))
      (simplicialDiagonalFunctor.map (weakStringMultiPostcomp f q 1))
      (relativeSWeakStringMultiComparison q) :=
  ⟨(relativeSWeakStringMultiComparison_postcomp f q).symm⟩

end SerrePositivity.KST.Fibration
