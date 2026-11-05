module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeUnitCapIntervalTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.TriangleDiagramParameterTransport
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModelUnitCollarTriangle
/-! # 主経路 Hom 模型上の係数側六三角形図式

概要：六つの実写像空間三角形を主経路の関手単体集合へ移し、共有辺と実補正対角を保つ。
方針：同じ Hom 模型同型の逆で入力を輸送して curry する。
規約：六二単体・共有辺・元入力を変更しない。
使われ方：係数 path を含む高次貼り合わせから指定対角境界の合成等式を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

def dgGluingModelUnitCapTriangleDiagram (i : Fin 6) :=
  dgGluingTriangleDiagramTransport (dgGluingNativeHomModelIso R C D M X Y).inv
    (dgGluingNativeUnitCapIntervalTriangle R C D M X Y i)

lemma dgGluingModelUnitCapTriangleDiagram_first_diagonal :
    stdSimplex.δ (1 : Fin 3) ≫ dgGluingModelUnitCapTriangleDiagram R C D M X Y 0 =
      stdSimplex.δ (1 : Fin 3) ≫ dgGluingModelUnitCapTriangleDiagram R C D M X Y 1 :=
  dgGluingTriangleDiagramTransport_face_eq _ _ _ _ _
    (dgGluingNativeUnitCapIntervalTriangle_first_diagonal R C D M X Y)

lemma dgGluingModelUnitCapTriangleDiagram_last_diagonal :
    stdSimplex.δ (1 : Fin 3) ≫ dgGluingModelUnitCapTriangleDiagram R C D M X Y 2 =
      stdSimplex.δ (1 : Fin 3) ≫ dgGluingModelUnitCapTriangleDiagram R C D M X Y 3 :=
  dgGluingTriangleDiagramTransport_face_eq _ _ _ _ _
    (dgGluingNativeUnitCapIntervalTriangle_last_diagonal R C D M X Y)

lemma dgGluingModelUnitCapTriangleDiagram_first_bridge :
    stdSimplex.δ (2 : Fin 3) ≫ dgGluingModelUnitCapTriangleDiagram R C D M X Y 1 =
      stdSimplex.δ (2 : Fin 3) ≫ dgGluingModelUnitCapTriangleDiagram R C D M X Y 5 :=
  dgGluingTriangleDiagramTransport_face_eq _ _ _ _ _
    (dgGluingNativeUnitCapIntervalTriangle_first_bridge R C D M X Y)

lemma dgGluingModelUnitCapTriangleDiagram_last_bridge :
    stdSimplex.δ (0 : Fin 3) ≫ dgGluingModelUnitCapTriangleDiagram R C D M X Y 3 =
      stdSimplex.δ (0 : Fin 3) ≫ dgGluingModelUnitCapTriangleDiagram R C D M X Y 5 :=
  dgGluingTriangleDiagramTransport_face_eq _ _ _ _ _
    (dgGluingNativeUnitCapIntervalTriangle_last_bridge R C D M X Y)

lemma dgGluingModelUnitCapTriangleDiagram_coefficient_first :
    stdSimplex.δ (0 : Fin 3) ≫ dgGluingModelUnitCapTriangleDiagram R C D M X Y 1 =
      stdSimplex.δ (0 : Fin 3) ≫ dgGluingModelUnitCapTriangleDiagram R C D M X Y 4 :=
  dgGluingTriangleDiagramTransport_face_eq _ _ _ _ _
    (dgGluingNativeUnitCapIntervalTriangle_coefficient_first R C D M X Y)

lemma dgGluingModelUnitCapTriangleDiagram_coefficient_last :
    stdSimplex.δ (2 : Fin 3) ≫ dgGluingModelUnitCapTriangleDiagram R C D M X Y 3 =
      stdSimplex.δ (2 : Fin 3) ≫ dgGluingModelUnitCapTriangleDiagram R C D M X Y 4 :=
  dgGluingTriangleDiagramTransport_face_eq _ _ _ _ _
    (dgGluingNativeUnitCapIntervalTriangle_coefficient_last R C D M X Y)

lemma dgGluingModelUnitCapTriangleDiagram_collar_bridge :
    stdSimplex.δ (1 : Fin 3) ≫ dgGluingModelUnitCapTriangleDiagram R C D M X Y 5 =
      stdSimplex.δ (1 : Fin 3) ≫ dgGluingModelUnitCollarTriangleDiagram R C D M X Y := by
  change _ = stdSimplex.δ (1 : Fin 3) ≫
    dgGluingTriangleDiagramTransport (dgGluingNativeHomModelIso R C D M X Y).inv
      (dgGluingNativeUnitCollarIntervalTriangle R C D M X Y)
  exact dgGluingTriangleDiagramTransport_face_eq _ _ _ _ _
    (dgGluingNativeUnitCapIntervalTriangle_collar_bridge R C D M X Y)

lemma dgGluingModelUnitCapTriangleDiagram_first_cap :
    stdSimplex.δ (2 : Fin 3) ≫ dgGluingModelUnitCapTriangleDiagram R C D M X Y 0 =
      curry (dgGluingPreCapModelInputPath R C D M X Y ≫
        dgGluingDerivedFirstCompositionInputDiagonal R C D M X Y) := by
  rw [dgGluingModelUnitCapTriangleDiagram, dgGluingTriangleDiagramTransport_face,
    dgGluingNativeUnitCapIntervalTriangle_first_cap R C D M X Y]
  apply congrArg curry
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

lemma dgGluingModelUnitCapTriangleDiagram_last_cap :
    stdSimplex.δ (0 : Fin 3) ≫ dgGluingModelUnitCapTriangleDiagram R C D M X Y 2 =
      curry (dgGluingExitCapModelInputPath R C D M X Y ≫
        dgGluingDerivedLastCompositionInputDiagonal R C D M X Y) := by
  rw [dgGluingModelUnitCapTriangleDiagram, dgGluingTriangleDiagramTransport_face,
    dgGluingNativeUnitCapIntervalTriangle_last_cap R C D M X Y]
  apply congrArg curry
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
end SerrePositivity.InfinityCategories
