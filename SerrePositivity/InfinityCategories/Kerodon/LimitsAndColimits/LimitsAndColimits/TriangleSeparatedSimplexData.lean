module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleLabelBaselineUnits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleLabelHomReplacement
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedMiddleHom

/-!
概要：元の可変な二短辺の基準単体に、分離座標で得た長 Hom を同じ対象で接続する。
方針：基準単体の端点の等号で Hom の表示を変更する。
規約：豊穣 Hom の宇宙は元のまま、K・L は対象宇宙で保持する。
使われ方：全次数の制御二胞体の豊穣関手データ。

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

/-- 元の二短辺を同じ K 単体で評価した基準単体。 -/
def triangleSeparatedBaseline {n : ℕ} (s : K _⦋n⦌) (t : Fin (n + 1) →o Fin 3) :
    (SimplicialNerve C) _⦋n⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelBaseline (f.app (Opposite.op ⦋n⦌) s).down
    (g.app (Opposite.op ⦋n⦌) s).down t

lemma triangleSeparatedBaseline_obj_zero {n : ℕ} (s : K _⦋n⦌)
    (t : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : t i = 0) :
    (triangleSeparatedBaseline f g s t).obj ⟨ULift.up i⟩ = X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelBaseline_obj_zero _ _ t i hi

lemma triangleSeparatedBaseline_obj_one {n : ℕ} (s : K _⦋n⦌)
    (t : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : t i = 1) :
    (triangleSeparatedBaseline f g s t).obj ⟨ULift.up i⟩ = Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelBaseline_obj_one _ _ t i hi

lemma triangleSeparatedBaseline_obj_two {n : ℕ} (s : K _⦋n⦌)
    (t : Fin (n + 1) →o Fin 3) (i : Fin (n + 1)) (hi : t i = 2) :
    (triangleSeparatedBaseline f g s t).obj ⟨ULift.up i⟩ = Z :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelBaseline_obj_two _ _ t i hi

variable (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶
  (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Z))

/-- 元の基準単体と同じ対象を持つ、零対象から終対象への新しい Hom。 -/
def triangleSeparatedReplacementHom {n : ℕ} (s : K _⦋n⦌) (r : L _⦋n⦌)
    (t : Fin (n + 1) →o Fin 3) (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 2) :
    nerve (Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) ⟶
      SimplicialCategory.sHom ((triangleSeparatedBaseline f g s t).obj ⟨ULift.up i⟩)
        ((triangleSeparatedBaseline f g s t).obj ⟨ULift.up j⟩) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom M s r t hi j ≫
    eqToHom (congrArg₂ SimplicialCategory.sHom
      (triangleSeparatedBaseline_obj_zero f g s t i hi).symm
      (triangleSeparatedBaseline_obj_two f g s t j hj).symm)

/-- 表示を元の X・Z へ戻すと、同じ小さい長 Hom の全作用を厳密に回収する。 -/
lemma triangleSeparatedReplacementHom_normalized {n : ℕ} (s : K _⦋n⦌) (r : L _⦋n⦌)
    (t : Fin (n + 1) →o Fin 3) (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 2) :
    triangleSeparatedReplacementHom f g M s r t i j hi hj ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (triangleSeparatedBaseline_obj_zero f g s t i hi)
        (triangleSeparatedBaseline_obj_two f g s t j hj)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom M s r t hi j := by
  simp only [triangleSeparatedReplacementHom, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
