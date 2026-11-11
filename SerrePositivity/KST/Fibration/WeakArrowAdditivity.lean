module
public import SerrePositivity.KST.Fibration.WeakArrowEquivalence
public import SerrePositivity.KST.SConstruction.RelativeMultiRealizationAdditivity

/-! # W 辺図式に対する正の全有限反復加法性

元の相対 cofiber 射影の完全な逆を通して、K-1 の相対加法性を W 辺図式に移す。
二射影は同じ選択した cofiber 図式の元の subobject・quotient 評価である。
W 辺の列の単体的構造に関する自然性と実現の fiber 比較は別工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 同じ cofiber 補完を使う、W 辺図式の正有限反復実現からの射対。 -/
def weakArrowMultiAdditivityMap {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    (multiRealizationFunctor (r + 1)).obj (weakArrowModel q) ⟶
      (multiRealizationFunctor (r + 1)).obj
        (closedStableModel (ClosedStablePredicate.top (sInputModel B))) ⊗
      (multiRealizationFunctor (r + 1)).obj (closedStableModel (kernelClosedPredicate q)) :=
  (multiRealizationFunctor (r + 1)).map (weakArrowCofiberEquivalence q).inv ≫
    relativeMultiRealizationAdditivityMap (r + 1)
      (ClosedStablePredicate.top (sInputModel B)) (kernelClosedPredicate q)

/-- W 辺図式の実現の射対は、全ての正有限反復で局所化同型。 -/
theorem weakArrowMultiAdditivityMap_localized_isIso
    {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (weakArrowMultiAdditivityMap q r)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map (weakArrowCofiberEquivalence q).inv)) :=
    multiRealization_map_localized_isIso_of_equivalence r (weakArrowCofiberEquivalence q).symm
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeMultiRealizationAdditivityMap (r + 1)
        (ClosedStablePredicate.top (sInputModel B)) (kernelClosedPredicate q))) :=
    relativeMultiRealizationAdditivityMap_localized_isIso r
      (ClosedStablePredicate.top (sInputModel B)) (kernelClosedPredicate q)
  unfold weakArrowMultiAdditivityMap
  rw [Functor.map_comp]
  infer_instance

/-- 第一射影は同じ補完の元の subobject 評価である。 -/
lemma weakArrowMultiAdditivityMap_fst {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    weakArrowMultiAdditivityMap q r ≫ fst _ _ =
      (multiRealizationFunctor (r + 1)).map (weakArrowCofiberEquivalence q).inv ≫
        (multiRealizationFunctor (r + 1)).map
          (relativeCofiberSubobject (ClosedStablePredicate.top (sInputModel B))
            (kernelClosedPredicate q)) := by
  exact Category.assoc _ _ _ |>.trans (congrArg
    ((multiRealizationFunctor (r + 1)).map (weakArrowCofiberEquivalence q).inv ≫ ·)
      (CartesianMonoidalCategory.lift_fst _ _))

/-- 第二射影は同じ補完の元の quotient 評価である。 -/
lemma weakArrowMultiAdditivityMap_snd {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (r : ℕ) :
    weakArrowMultiAdditivityMap q r ≫ snd _ _ =
      (multiRealizationFunctor (r + 1)).map (weakArrowCofiberEquivalence q).inv ≫
        (multiRealizationFunctor (r + 1)).map
          (relativeCofiberQuotient (ClosedStablePredicate.top (sInputModel B))
            (kernelClosedPredicate q)) := by
  exact Category.assoc _ _ _ |>.trans (congrArg
    ((multiRealizationFunctor (r + 1)).map (weakArrowCofiberEquivalence q).inv ≫ ·)
      (CartesianMonoidalCategory.lift_snd _ _))

end SerrePositivity.KST.Fibration
