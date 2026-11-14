module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Composition.HomTargetUnitTriangleFamilies
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.TriangleDiagramParameterTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Composition.HomTargetUnitCapIntervalTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Composition.HomTargetUnitCollarIntervalTriangle
/-!
概要：元 Hom 入力上の関手単体集合へ六片と collar 三角形を移す。
方針：元の全入力・指定面・全区間族を保持する比較を合成する。
規約：追加の主経路仮定を置かない。使われ方：元 lax Hom 比較の逆の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetHomParameter R C D E p q X Y
attribute [local irreducible] dgHomGluingBimodule

def dgGluingHomTargetUnitCollarTriangleDiagram :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleDiagramTransport (𝟙 P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCollarIntervalTriangle R C D E p q X Y)

lemma dgGluingHomTargetUnitCollarTriangleDiagram_two :
    stdSimplex.δ (2 : Fin 3) ≫ dgGluingHomTargetUnitCollarTriangleDiagram R C D E p q X Y =
      curry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreNormalizationInputPath R C D E p q X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputDiagonal R C D E p q X Y) := by
  rw [dgGluingHomTargetUnitCollarTriangleDiagram, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleDiagramTransport_face,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCollarIntervalTriangle_two R C D E p q X Y]
  apply congrArg curry
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

lemma dgGluingHomTargetUnitCollarTriangleDiagram_zero :
    stdSimplex.δ (0 : Fin 3) ≫ dgGluingHomTargetUnitCollarTriangleDiagram R C D E p q X Y =
      curry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCollarInputPath R C D E p q X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputDiagonal R C D E p q X Y) := by
  rw [dgGluingHomTargetUnitCollarTriangleDiagram, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleDiagramTransport_face,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCollarIntervalTriangle_zero R C D E p q X Y]
  apply congrArg curry
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

def dgGluingHomTargetUnitCapTriangleDiagram (i : Fin 6) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleDiagramTransport (𝟙 P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapIntervalTriangle R C D E p q X Y i)

lemma dgGluingHomTargetUnitCapTriangleDiagram_first_diagonal :
    stdSimplex.δ (1 : Fin 3) ≫ dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 0 =
      stdSimplex.δ (1 : Fin 3) ≫ dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 1 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleDiagramTransport_face_eq _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapIntervalTriangle_first_diagonal R C D E p q X Y)

lemma dgGluingHomTargetUnitCapTriangleDiagram_last_diagonal :
    stdSimplex.δ (1 : Fin 3) ≫ dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 2 =
      stdSimplex.δ (1 : Fin 3) ≫ dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 3 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleDiagramTransport_face_eq _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapIntervalTriangle_last_diagonal R C D E p q X Y)

lemma dgGluingHomTargetUnitCapTriangleDiagram_first_bridge :
    stdSimplex.δ (2 : Fin 3) ≫ dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 1 =
      stdSimplex.δ (2 : Fin 3) ≫ dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 5 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleDiagramTransport_face_eq _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapIntervalTriangle_first_bridge R C D E p q X Y)

lemma dgGluingHomTargetUnitCapTriangleDiagram_last_bridge :
    stdSimplex.δ (0 : Fin 3) ≫ dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 3 =
      stdSimplex.δ (0 : Fin 3) ≫ dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 5 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleDiagramTransport_face_eq _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapIntervalTriangle_last_bridge R C D E p q X Y)

lemma dgGluingHomTargetUnitCapTriangleDiagram_coefficient_first :
    stdSimplex.δ (0 : Fin 3) ≫ dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 1 =
      stdSimplex.δ (0 : Fin 3) ≫ dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 4 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleDiagramTransport_face_eq _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapIntervalTriangle_coefficient_first R C D E p q X Y)

lemma dgGluingHomTargetUnitCapTriangleDiagram_coefficient_last :
    stdSimplex.δ (2 : Fin 3) ≫ dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 3 =
      stdSimplex.δ (2 : Fin 3) ≫ dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 4 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleDiagramTransport_face_eq _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapIntervalTriangle_coefficient_last R C D E p q X Y)

lemma dgGluingHomTargetUnitCapTriangleDiagram_collar_bridge :
    stdSimplex.δ (1 : Fin 3) ≫ dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 5 =
      stdSimplex.δ (1 : Fin 3) ≫ dgGluingHomTargetUnitCollarTriangleDiagram R C D E p q X Y := by
  change _ = stdSimplex.δ (1 : Fin 3) ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleDiagramTransport (𝟙 P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCollarIntervalTriangle R C D E p q X Y)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleDiagramTransport_face_eq _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapIntervalTriangle_collar_bridge R C D E p q X Y)

lemma dgGluingHomTargetUnitCapTriangleDiagram_first_cap :
    stdSimplex.δ (2 : Fin 3) ≫ dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 0 =
      curry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetPreCapInputPath R C D E p q X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetFirstInputDiagonal R C D E p q X Y) := by
  rw [dgGluingHomTargetUnitCapTriangleDiagram, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleDiagramTransport_face,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapIntervalTriangle_first_cap R C D E p q X Y]
  apply congrArg curry
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

lemma dgGluingHomTargetUnitCapTriangleDiagram_last_cap :
    stdSimplex.δ (0 : Fin 3) ≫ dgGluingHomTargetUnitCapTriangleDiagram R C D E p q X Y 2 =
      curry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetExitCapInputPath R C D E p q X Y ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLastInputDiagonal R C D E p q X Y) := by
  rw [dgGluingHomTargetUnitCapTriangleDiagram, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleDiagramTransport_face,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetUnitCapIntervalTriangle_last_cap R C D E p q X Y]
  apply congrArg curry
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
