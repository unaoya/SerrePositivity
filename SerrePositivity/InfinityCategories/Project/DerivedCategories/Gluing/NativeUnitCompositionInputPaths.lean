module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeUnitCompositionPaths
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CompositionInputTriangleEvaluations

/-! # 元 Hom の二射影を保つ native 入力 fiber 内の四変形

概要：四つの実合成対応内の道を、元の左右 Hom 鎖射影付き fiber へ持ち上げる。
方針：正本係数入力の因子分解を使い、同じ元射影を時間方向に一定に保つ。
規約：元入力・実三角形の評価・両端を厳密に保持する。
使われ方：共通補正端と選択済み二変形を、基底全体を固定した相対二次元比較へ供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePinchedHomParameter R C D M X Y

def dgGluingNativePreCollarInputPath : P ⊗ Δ[1] ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputFiber R C D M X Y :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCollarCompositionPath R C D M X Y)
    (fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y))) (by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCollarCompositionPath_input R C D M X Y,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedRightCoefficientInput_raw_factor R C D M X Y]
      simp only [Category.assoc])

lemma dgGluingNativePreCollarInputPath_composition :
    dgGluingNativePreCollarInputPath R C D M X Y ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCollarCompositionPath R C D M X Y :=
  pullback.lift_fst _ _ _

lemma dgGluingNativePreCollarInputPath_input :
    dgGluingNativePreCollarInputPath R C D M X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputProjection R C D M X Y =
      fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y)) :=
  pullback.lift_snd _ _ _

lemma dgGluingNativePreCollarInputPath_evaluation :
    (Δ[2] ◁ dgGluingNativePreCollarInputPath R C D M X Y) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstInputTriangleEvaluation R C D M X Y =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeUnitCollarTriangleFamily R C D M X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstInputTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingNativePreCollarInputPath_composition R C D M X Y,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCollarCompositionPath_evaluation R C D M X Y]

def dgGluingNativePreCollarInputHomotopy :
    SSet.Homotopy (ι₀ ≫ dgGluingNativePreCollarInputPath R C D M X Y)
      (ι₁ ≫ dgGluingNativePreCollarInputPath R C D M X Y) where
  h := dgGluingNativePreCollarInputPath R C D M X Y
  h₀ := rfl
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

lemma dgGluingNativePreCollarInputHomotopy_over :
    (dgGluingNativePreCollarInputHomotopy R C D M X Y).h ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputProjection R C D M X Y =
      fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y)) :=
  dgGluingNativePreCollarInputPath_input R C D M X Y

def dgGluingNativePreCapInputPath : P ⊗ Δ[1] ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputFiber R C D M X Y :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCapCompositionPath R C D M X Y)
    (fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y))) (by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCapCompositionPath_input R C D M X Y,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedRightCoefficientInput_raw_factor R C D M X Y]
      simp only [Category.assoc])

lemma dgGluingNativePreCapInputPath_composition :
    dgGluingNativePreCapInputPath R C D M X Y ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCapCompositionPath R C D M X Y :=
  pullback.lift_fst _ _ _

lemma dgGluingNativePreCapInputPath_input :
    dgGluingNativePreCapInputPath R C D M X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputProjection R C D M X Y =
      fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y)) :=
  pullback.lift_snd _ _ _

lemma dgGluingNativePreCapInputPath_evaluation :
    (Δ[2] ◁ dgGluingNativePreCapInputPath R C D M X Y) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstInputTriangleEvaluation R C D M X Y =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreUnitCapTriangleFamily R C D M X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstInputTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingNativePreCapInputPath_composition R C D M X Y,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCapCompositionPath_evaluation R C D M X Y]

def dgGluingNativePreCapInputHomotopy :
    SSet.Homotopy (ι₀ ≫ dgGluingNativePreCapInputPath R C D M X Y)
      (ι₁ ≫ dgGluingNativePreCapInputPath R C D M X Y) where
  h := dgGluingNativePreCapInputPath R C D M X Y
  h₀ := rfl
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

lemma dgGluingNativePreCapInputHomotopy_over :
    (dgGluingNativePreCapInputHomotopy R C D M X Y).h ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputProjection R C D M X Y =
      fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y)) :=
  dgGluingNativePreCapInputPath_input R C D M X Y

def dgGluingNativeExitCollarInputPath : P ⊗ Δ[1] ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputFiber R C D M X Y :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCollarCompositionPath R C D M X Y)
    (fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y))) (by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCollarCompositionPath_input R C D M X Y,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLeftCoefficientInput_raw_factor R C D M X Y]
      simp only [Category.assoc])

lemma dgGluingNativeExitCollarInputPath_composition :
    dgGluingNativeExitCollarInputPath R C D M X Y ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCollarCompositionPath R C D M X Y :=
  pullback.lift_fst _ _ _

lemma dgGluingNativeExitCollarInputPath_input :
    dgGluingNativeExitCollarInputPath R C D M X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputProjection R C D M X Y =
      fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y)) :=
  pullback.lift_snd _ _ _

lemma dgGluingNativeExitCollarInputPath_evaluation :
    (Δ[2] ◁ dgGluingNativeExitCollarInputPath R C D M X Y) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastInputTriangleEvaluation R C D M X Y =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitUnitCollarTriangleFamily R C D M X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastInputTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingNativeExitCollarInputPath_composition R C D M X Y,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCollarCompositionPath_evaluation R C D M X Y]

def dgGluingNativeExitCollarInputHomotopy :
    SSet.Homotopy (ι₀ ≫ dgGluingNativeExitCollarInputPath R C D M X Y)
      (ι₁ ≫ dgGluingNativeExitCollarInputPath R C D M X Y) where
  h := dgGluingNativeExitCollarInputPath R C D M X Y
  h₀ := rfl
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

lemma dgGluingNativeExitCollarInputHomotopy_over :
    (dgGluingNativeExitCollarInputHomotopy R C D M X Y).h ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputProjection R C D M X Y =
      fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y)) :=
  dgGluingNativeExitCollarInputPath_input R C D M X Y

def dgGluingNativeExitCapInputPath : P ⊗ Δ[1] ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputFiber R C D M X Y :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCapCompositionPath R C D M X Y)
    (fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y))) (by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCapCompositionPath_input R C D M X Y,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomDerivedLeftCoefficientInput_raw_factor R C D M X Y]
      simp only [Category.assoc])

lemma dgGluingNativeExitCapInputPath_composition :
    dgGluingNativeExitCapInputPath R C D M X Y ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCapCompositionPath R C D M X Y :=
  pullback.lift_fst _ _ _

lemma dgGluingNativeExitCapInputPath_input :
    dgGluingNativeExitCapInputPath R C D M X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputProjection R C D M X Y =
      fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y)) :=
  pullback.lift_snd _ _ _

lemma dgGluingNativeExitCapInputPath_evaluation :
    (Δ[2] ◁ dgGluingNativeExitCapInputPath R C D M X Y) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastInputTriangleEvaluation R C D M X Y =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitUnitCapTriangleFamily R C D M X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastInputTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingNativeExitCapInputPath_composition R C D M X Y,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCapCompositionPath_evaluation R C D M X Y]

def dgGluingNativeExitCapInputHomotopy :
    SSet.Homotopy (ι₀ ≫ dgGluingNativeExitCapInputPath R C D M X Y)
      (ι₁ ≫ dgGluingNativeExitCapInputPath R C D M X Y) where
  h := dgGluingNativeExitCapInputPath R C D M X Y
  h₀ := rfl
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

lemma dgGluingNativeExitCapInputHomotopy_over :
    (dgGluingNativeExitCapInputHomotopy R C D M X Y).h ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputProjection R C D M X Y =
      fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y)) :=
  dgGluingNativeExitCapInputPath_input R C D M X Y
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
