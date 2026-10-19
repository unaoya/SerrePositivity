module

public import SerrePositivity.InfinityCategories.F1.VertexIsoMapCoherence
public import SerrePositivity.InfinityCategories.F1.TransportRepresentationComparisonCoherence
public import SerrePositivity.InfinityCategories.F1.TransportWitnessBoundaryDiagram

/-!
概要：表現空間の cartesian な比較を通常の図式の前合成と同定する。
方針：表現空間の図式射影の可換式を頂点同型の像へ移す。
規約：同じ表現の比較を全パラメーターで制限する。
使われ方：余単位の自然性を通常の前合成の可換式で表す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：cartesian 制限の比較を分類図式へ写すと元の図式同型の前合成。
方針：二つの射の合成の像と表現空間の図式射影の可換式を使う。
規約：図式と比較の選択を変えず実際の同型の等式を与える。
使われ方：余単位の制限の三角形を自然性の式へ移す。 -/
lemma LeftTransportRepresentation.cartesianRestrict_diagramIso
    {E F B D : SSet.{u + 1}} {p : E ⟶ B} {q : F ⟶ D}
    [LeftFibration p] [LeftFibration q] (R S : LeftTransportRepresentation p)
    (a : VertexIso (transportWitnessVertex R) (transportWitnessVertex S))
    (e : F ⟶ E) (g : D ⟶ B) (h : IsPullback e q p g) :
    (R.cartesianRestrict e g h).diagramIso (S.cartesianRestrict e g h)
      (R.cartesianRestrictVertexIso S a e g h) = (R.diagramIso S a).precomp g := by
  let f : Arrow.mk q ⟶ Arrow.mk p := Arrow.homMk e g h.w
  have : LeftFibration (Arrow.mk q).hom := by change LeftFibration q; infer_instance
  have : LeftFibration (Arrow.mk p).hom := by change LeftFibration p; infer_instance
  have hd := transportWitnessPre_diagram f h
  have ha := vertexIso_map_congr a
    (transportWitnessPre f h ≫ transportWitnessDiagram q)
    (transportWitnessDiagram p ≫ (pre g).app SpaceInfinity) hd
  unfold LeftTransportRepresentation.diagramIso
    LeftTransportRepresentation.cartesianRestrictVertexIso FunctorIso.precomp
  simp only [vertexIso_map_trans, vertexIso_map_symm, vertexIso_map_comp]
  rw [ha]
  apply Iso.ext
  simp [VertexIso.map, eqToHom_map]

end SerrePositivity.InfinityCategories
