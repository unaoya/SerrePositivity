module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeUnitCompositionInputPaths
/-! # 主経路の Hom 模型上の元入力固定四変形

概要：native 四変形を同じ Hom 模型同型の逆で移し、主経路の左右鎖射影を全時間で固定する。
方針：元 pinched Hom と元複体模型の実同型を使い、二脚の因子分解を相殺する。
規約：元の複体・元入力・実三角形族を変更しない。
使われ方：選択済みの第一・第二変形と直接同じ fiber・同じパラメーターで比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
private lemma dgGluingIsoInputPath_precomp {P K E B : SSet.{u}} (e : P ≅ K) (V : P ⊗ Δ[1] ⟶ E)
    (p : E ⟶ B) (a : K ⟶ B)
    (h : V ≫ p = fst P (Δ[1] : SSet.{u}) ≫ e.hom ≫ a) :
    ((e.inv ▷ (Δ[1] : SSet.{u})) ≫ V) ≫ p = fst K (Δ[1] : SSet.{u}) ≫ a := by
  rw [Category.assoc, h, ← Category.assoc, whiskerRight_fst]
  simp only [Category.assoc]
  rw [← Category.assoc e.inv e.hom a, e.inv_hom_id, Category.id_comp]
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
def dgGluingNativeHomModelIso : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePinchedHomParameter R C D M X Y ≅
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y)) :=
  (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).mapIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso (A := R) X Y)
lemma dgGluingNativeHomModelIso_hom : (dgGluingNativeHomModelIso R C D M X Y).hom =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelMap R C D M X Y := rfl


def dgGluingPreCollarModelInputPath :=
  ((dgGluingNativeHomModelIso R C D M X Y).inv ▷ Δ[1]) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCollarInputPath R C D M X Y

lemma dgGluingPreCollarModelInputPath_input :
    dgGluingPreCollarModelInputPath R C D M X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputProjection R C D M X Y =
      fst _ (Δ[1] : SSet.{max (u + 1) v w}) ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y)) := by
  apply dgGluingIsoInputPath_precomp (dgGluingNativeHomModelIso R C D M X Y)
  simpa only [dgGluingNativeHomModelIso_hom] using
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCollarInputPath_input R C D M X Y

lemma dgGluingPreCollarModelInputPath_evaluation :
    (Δ[2] ◁ dgGluingPreCollarModelInputPath R C D M X Y) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstInputTriangleEvaluation R C D M X Y =
      (Δ[2] ◁ ((dgGluingNativeHomModelIso R C D M X Y).inv ▷ Δ[1])) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreNormalizeUnitCollarTriangleFamily R C D M X Y := by
  rw [dgGluingPreCollarModelInputPath, whiskerLeft_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCollarInputPath_evaluation R C D M X Y]

def dgGluingPreCollarModelInputHomotopy :
    SSet.Homotopy (ι₀ ≫ dgGluingPreCollarModelInputPath R C D M X Y)
      (ι₁ ≫ dgGluingPreCollarModelInputPath R C D M X Y) where
  h := dgGluingPreCollarModelInputPath R C D M X Y
  h₀ := rfl
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

lemma dgGluingPreCollarModelInputHomotopy_over :
    (dgGluingPreCollarModelInputHomotopy R C D M X Y).h ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputProjection R C D M X Y =
      fst _ (Δ[1] : SSet.{max (u + 1) v w}) ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y)) :=
  dgGluingPreCollarModelInputPath_input R C D M X Y

def dgGluingPreCapModelInputPath :=
  ((dgGluingNativeHomModelIso R C D M X Y).inv ▷ Δ[1]) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCapInputPath R C D M X Y

lemma dgGluingPreCapModelInputPath_input :
    dgGluingPreCapModelInputPath R C D M X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputProjection R C D M X Y =
      fst _ (Δ[1] : SSet.{max (u + 1) v w}) ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y)) := by
  apply dgGluingIsoInputPath_precomp (dgGluingNativeHomModelIso R C D M X Y)
  simpa only [dgGluingNativeHomModelIso_hom] using
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCapInputPath_input R C D M X Y

lemma dgGluingPreCapModelInputPath_evaluation :
    (Δ[2] ◁ dgGluingPreCapModelInputPath R C D M X Y) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstInputTriangleEvaluation R C D M X Y =
      (Δ[2] ◁ ((dgGluingNativeHomModelIso R C D M X Y).inv ▷ Δ[1])) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreUnitCapTriangleFamily R C D M X Y := by
  rw [dgGluingPreCapModelInputPath, whiskerLeft_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePreCapInputPath_evaluation R C D M X Y]

def dgGluingPreCapModelInputHomotopy :
    SSet.Homotopy (ι₀ ≫ dgGluingPreCapModelInputPath R C D M X Y)
      (ι₁ ≫ dgGluingPreCapModelInputPath R C D M X Y) where
  h := dgGluingPreCapModelInputPath R C D M X Y
  h₀ := rfl
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

lemma dgGluingPreCapModelInputHomotopy_over :
    (dgGluingPreCapModelInputHomotopy R C D M X Y).h ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputProjection R C D M X Y =
      fst _ (Δ[1] : SSet.{max (u + 1) v w}) ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRightHomMap R C D M X Y)) :=
  dgGluingPreCapModelInputPath_input R C D M X Y

def dgGluingExitCollarModelInputPath :=
  ((dgGluingNativeHomModelIso R C D M X Y).inv ▷ Δ[1]) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCollarInputPath R C D M X Y

lemma dgGluingExitCollarModelInputPath_input :
    dgGluingExitCollarModelInputPath R C D M X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputProjection R C D M X Y =
      fst _ (Δ[1] : SSet.{max (u + 1) v w}) ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y)) := by
  apply dgGluingIsoInputPath_precomp (dgGluingNativeHomModelIso R C D M X Y)
  simpa only [dgGluingNativeHomModelIso_hom] using
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCollarInputPath_input R C D M X Y

lemma dgGluingExitCollarModelInputPath_evaluation :
    (Δ[2] ◁ dgGluingExitCollarModelInputPath R C D M X Y) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastInputTriangleEvaluation R C D M X Y =
      (Δ[2] ◁ ((dgGluingNativeHomModelIso R C D M X Y).inv ▷ Δ[1])) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitUnitCollarTriangleFamily R C D M X Y := by
  rw [dgGluingExitCollarModelInputPath, whiskerLeft_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCollarInputPath_evaluation R C D M X Y]

def dgGluingExitCollarModelInputHomotopy :
    SSet.Homotopy (ι₀ ≫ dgGluingExitCollarModelInputPath R C D M X Y)
      (ι₁ ≫ dgGluingExitCollarModelInputPath R C D M X Y) where
  h := dgGluingExitCollarModelInputPath R C D M X Y
  h₀ := rfl
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

lemma dgGluingExitCollarModelInputHomotopy_over :
    (dgGluingExitCollarModelInputHomotopy R C D M X Y).h ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputProjection R C D M X Y =
      fst _ (Δ[1] : SSet.{max (u + 1) v w}) ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y)) :=
  dgGluingExitCollarModelInputPath_input R C D M X Y

def dgGluingExitCapModelInputPath :=
  ((dgGluingNativeHomModelIso R C D M X Y).inv ▷ Δ[1]) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCapInputPath R C D M X Y

lemma dgGluingExitCapModelInputPath_input :
    dgGluingExitCapModelInputPath R C D M X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputProjection R C D M X Y =
      fst _ (Δ[1] : SSet.{max (u + 1) v w}) ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y)) := by
  apply dgGluingIsoInputPath_precomp (dgGluingNativeHomModelIso R C D M X Y)
  simpa only [dgGluingNativeHomModelIso_hom] using
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCapInputPath_input R C D M X Y

lemma dgGluingExitCapModelInputPath_evaluation :
    (Δ[2] ◁ dgGluingExitCapModelInputPath R C D M X Y) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastInputTriangleEvaluation R C D M X Y =
      (Δ[2] ◁ ((dgGluingNativeHomModelIso R C D M X Y).inv ▷ Δ[1])) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitUnitCapTriangleFamily R C D M X Y := by
  rw [dgGluingExitCapModelInputPath, whiskerLeft_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeExitCapInputPath_evaluation R C D M X Y]

def dgGluingExitCapModelInputHomotopy :
    SSet.Homotopy (ι₀ ≫ dgGluingExitCapModelInputPath R C D M X Y)
      (ι₁ ≫ dgGluingExitCapModelInputPath R C D M X Y) where
  h := dgGluingExitCapModelInputPath R C D M X Y
  h₀ := rfl
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

lemma dgGluingExitCapModelInputHomotopy_over :
    (dgGluingExitCapModelInputHomotopy R C D M X Y).h ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputProjection R C D M X Y =
      fst _ (Δ[1] : SSet.{max (u + 1) v w}) ≫ (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftHomMap R C D M X Y)) :=
  dgGluingExitCapModelInputPath_input R C D M X Y
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
