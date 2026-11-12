module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedSimplexData

/-!
概要：長 Hom を置換した全 Hom データを、元の三対象へ正規化して計算する。
方針：変更しない Hom は基準単体の式、変更箇所は指定長 Hom の式を使う。
規約：二短辺の元の全単体を保持する。
使われ方：再構成単体の三種類の内部合成条件。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C}
  {K L : SSet.{max u v}}
  (f : K ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y))
  (g : K ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z))
  (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Z))
  {n : ℕ} (s : K _⦋n⦌) (r : L _⦋n⦌) (t : Fin (n + 1) →o Fin 3)

def triangleSeparatedAssignedHom (i j : Fin (n + 1)) :
    nerve (Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) ⟶
      SimplicialCategory.sHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline f g s t).obj ⟨ULift.up i⟩)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline f g s t).obj ⟨ULift.up j⟩) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelReplacedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline f g s t) t
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedReplacementHom f g M s r t) i j

lemma triangleSeparatedAssignedHom_zero (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 0) :
    triangleSeparatedAssignedHom f g M s r t i j ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_zero f g s t i hi)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_zero f g s t j hj)) =
      CartesianMonoidalCategory.toUnit _ ≫ eId SSet X := by
  rw [triangleSeparatedAssignedHom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelReplacedHom_proper _ _ _ i j (by omega)]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelBaseline_zeroHom _ _ t i j hi hj

lemma triangleSeparatedAssignedHom_two (i j : Fin (n + 1)) (hi : t i = 2) (hj : t j = 2) :
    triangleSeparatedAssignedHom f g M s r t i j ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_two f g s t i hi)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_two f g s t j hj)) =
      CartesianMonoidalCategory.toUnit _ ≫ eId SSet Z := by
  rw [triangleSeparatedAssignedHom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelReplacedHom_proper _ _ _ i j (by omega)]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelBaseline_twoHom _ _ t i j hi hj

lemma triangleSeparatedAssignedHom_long (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 2) :
    triangleSeparatedAssignedHom f g M s r t i j ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_zero f g s t i hi)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_two f g s t j hj)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom M s r t hi j := by
  rw [triangleSeparatedAssignedHom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelReplacedHom_full _ _ _ i j hi hj]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedReplacementHom_normalized f g M s r t i j hi hj

lemma triangleSeparatedAssignedHom_first (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 1) :
    triangleSeparatedAssignedHom f g M s r t i j ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_zero f g s t i hi)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_one f g s t j hj)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel t) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleZeroLabel_zero t hi) j) s f := by
  rw [triangleSeparatedAssignedHom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelReplacedHom_proper _ _ _ i j (by omega)]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedHom_at_simplex]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelBaseline_firstHom _ _ t i j hi hj

lemma triangleSeparatedAssignedHom_last (i j : Fin (n + 1)) (hi : t i = 1) (hj : t j = 2) :
    triangleSeparatedAssignedHom f g M s r t i j ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_one f g s t i hi)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_two f g s t j hj)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutLastZeroMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel t)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleUpperLabel_zero_of_ne t (i := i) (by omega)) j) s g := by
  rw [triangleSeparatedAssignedHom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelReplacedHom_proper _ _ _ i j (by omega)]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLiftedHom_at_simplex]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelBaseline_lastHom _ _ t i j hi hj

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
