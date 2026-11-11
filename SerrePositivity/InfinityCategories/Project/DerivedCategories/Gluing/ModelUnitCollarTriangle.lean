module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeUnitCollarIntervalTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NativeUnitInputModelPaths
/-! # 主経路 Hom 模型上の実補正対角三角形

概要：同じ導来写像空間三角形を主経路の Hom 模型へ移し、二面を実補正道として保持する。
方針：元 Hom 模型同型の逆で全入力を輸送してから curry する。
規約：対角道の全時間と同じ三角形を保持する。
使われ方：左右補正道の合成を、選択済み二変形を含む高次比較へ供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativePinchedHomParameter R C D M X Y
def dgGluingModelUnitCollarParameter : SSet.{max (u + 1) v w} :=
  (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max u v w} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M X Y))
local notation "K" => dgGluingModelUnitCollarParameter R C D M X Y

def dgGluingModelUnitCollarIntervalTriangle :=
  (Δ[2] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelIso R C D M X Y).inv) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCollarIntervalTriangle R C D M X Y

def dgGluingModelUnitCollarTriangleDiagram :=
  curry ((β_ K (Δ[2] : SSet.{max (u + 1) v w})).hom ≫
    dgGluingModelUnitCollarIntervalTriangle R C D M X Y)

lemma dgGluingModelUnitCollarIntervalTriangle_two :
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ dgGluingModelUnitCollarIntervalTriangle R C D M X Y =
      (β_ (Δ[1] : SSet.{max (u + 1) v w}) K).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreCollarModelInputPath R C D M X Y ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y := by
  calc
    _ = (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelIso R C D M X Y).inv) ≫
        (stdSimplex.δ (2 : Fin 3) ▷ P) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCollarIntervalTriangle R C D M X Y := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCollarIntervalTriangle_two R C D M X Y]
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl

lemma dgGluingModelUnitCollarTriangleDiagram_two :
    stdSimplex.δ (2 : Fin 3) ≫ dgGluingModelUnitCollarTriangleDiagram R C D M X Y =
      curry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreCollarModelInputPath R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y) := by
  rw [dgGluingModelUnitCollarTriangleDiagram, ← curry_natural_left]
  apply congrArg curry
  calc
    _ = (β_ K (Δ[1] : SSet.{max (u + 1) v w})).hom ≫
        (stdSimplex.δ (2 : Fin 3) ▷ K) ≫
          dgGluingModelUnitCollarIntervalTriangle R C D M X Y := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by
      rw [dgGluingModelUnitCollarIntervalTriangle_two R C D M X Y]
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl

lemma dgGluingModelUnitCollarIntervalTriangle_zero :
    (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ dgGluingModelUnitCollarIntervalTriangle R C D M X Y =
      (β_ (Δ[1] : SSet.{max (u + 1) v w}) K).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitCollarModelInputPath R C D M X Y ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal R C D M X Y := by
  calc
    _ = (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeHomModelIso R C D M X Y).inv) ≫
        (stdSimplex.δ (0 : Fin 3) ▷ P) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCollarIntervalTriangle R C D M X Y := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUnitCollarIntervalTriangle_zero R C D M X Y]
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl

lemma dgGluingModelUnitCollarTriangleDiagram_zero :
    stdSimplex.δ (0 : Fin 3) ≫ dgGluingModelUnitCollarTriangleDiagram R C D M X Y =
      curry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingExitCollarModelInputPath R C D M X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDerivedLastCompositionInputDiagonal R C D M X Y) := by
  rw [dgGluingModelUnitCollarTriangleDiagram, ← curry_natural_left]
  apply congrArg curry
  calc
    _ = (β_ K (Δ[1] : SSet.{max (u + 1) v w})).hom ≫
        (stdSimplex.δ (0 : Fin 3) ▷ K) ≫
          dgGluingModelUnitCollarIntervalTriangle R C D M X Y := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := by
      rw [dgGluingModelUnitCollarIntervalTriangle_zero R C D M X Y]
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
