module

public import SerrePositivity.InfinityCategories.F1.TransportRepresentationComparisonRestriction

/-!
概要：cartesian な比較の全空間側の作用と pointed な射の前合成を同定する。
方針：表現空間の pointed 射影の可換式を頂点同型の像へ移す。
規約：分類図式の比較と同じ頂点同型を使う。
使われ方：余単位の自然性と全空間比較を同時に保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：表現空間の cartesian 制限は pointed な射の前合成と可換。
方針：全部分複体の包含後に四角形空間の射影公式を使う。
規約：全高次パラメーターでの等式。
使われ方：全空間側の同型の自然性。 -/
lemma transportWitnessPre_pointed {p q : Arrow SSet.{u + 1}}
    [LeftFibration p.hom] [LeftFibration q.hom] (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right) :
    transportWitnessPre f hf ≫ transportWitnessPointed p.hom =
      transportWitnessPointed q.hom ≫ (pre f.left).app PointedSpaceInfinity := by
  rw [transportWitnessPointed, ← Category.assoc, transportWitnessPre_ι,
    Category.assoc, transportSquarePre_pointed]
  rfl

/-- 概要：cartesian 制限の pointed な比較は元の比較の全空間の射での前合成。
方針：図式側と同じ表現の比較を pointed な射影へ写す。
規約：制限の pointed な射の一致による端点の移送を明示する。
使われ方：図式側と全空間側を同時に保つ自然性の界面。 -/
lemma LeftTransportRepresentation.cartesianRestrict_pointedIso
    {E F B D : SSet.{u + 1}} {p : E ⟶ B} {q : F ⟶ D}
    [LeftFibration p] [LeftFibration q] (R S : LeftTransportRepresentation p)
    (a : VertexIso (transportWitnessVertex R) (transportWitnessVertex S))
    (e : F ⟶ E) (g : D ⟶ B) (h : IsPullback e q p g) :
    (R.cartesianRestrict e g h).pointedIso (S.cartesianRestrict e g h)
      (R.cartesianRestrictVertexIso S a e g h) =
      eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (functorVertex d))
        (R.cartesianRestrict_pointedMap e g h)) ≪≫ (R.pointedIso S a).precomp e ≪≫
      (eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (functorVertex d))
        (S.cartesianRestrict_pointedMap e g h))).symm := by
  let f : Arrow.mk q ⟶ Arrow.mk p := Arrow.homMk e g h.w
  have : LeftFibration (Arrow.mk q).hom := by change LeftFibration q; infer_instance
  have : LeftFibration (Arrow.mk p).hom := by change LeftFibration p; infer_instance
  have hd := transportWitnessPre_pointed f h
  have ha := vertexIso_map_congr a
    (transportWitnessPre f h ≫ transportWitnessPointed q)
    (transportWitnessPointed p ≫ (pre e).app PointedSpaceInfinity) hd
  unfold LeftTransportRepresentation.pointedIso
    LeftTransportRepresentation.cartesianRestrictVertexIso FunctorIso.precomp
  simp only [vertexIso_map_trans, vertexIso_map_symm, vertexIso_map_comp]
  rw [ha]
  apply Iso.ext
  simp [VertexIso.map, eqToHom_map]

end SerrePositivity.InfinityCategories
