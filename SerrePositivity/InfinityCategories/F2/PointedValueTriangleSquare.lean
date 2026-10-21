module

public import SerrePositivity.InfinityCategories.F2.PointedValueTriangleIso

/-!
概要：元の三角形同型と同じ区間輸送の path を、指定された両端比較の正方形で結ぶ。
方針：全 Hom の自然性の評価側だけを厳密な頂点等式で移し、元の指定類を回収する。
規約：三角形・全 path・指定比較を保持。使われ方：全錐の二三角形の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 評価側の二頂点だけを等式で移しても、元の指定辺と比較の可換式を保持する。 -/
lemma edgeIsoSquare_ofEq {Y : SSet.{u}} {x y x' y' z w : Y _⦋0⦌}
    (e : Y.Edge x y) (t : Y.Edge z w) (i : VertexIso x z) (j : VertexIso y w)
    (hx : x = x') (hy : y = y')
    (h : SSet.Truncated.HomotopyCategory.homMk e.toTruncated ≫ j.hom =
      i.hom ≫ SSet.Truncated.HomotopyCategory.homMk t.toTruncated) :
    SSet.Truncated.HomotopyCategory.homMk (e.ofEq hx hy).toTruncated ≫
        ((eqToIso (congrArg SSet.HomotopyCategory.mk hy)).symm ≪≫ j).hom =
      ((eqToIso (congrArg SSet.HomotopyCategory.mk hx)).symm ≪≫ i).hom ≫
        SSet.Truncated.HomotopyCategory.homMk t.toTruncated := by
  subst x' y'
  have he : e.ofEq rfl rfl = e := by
    apply SSet.Edge.ext
    rfl
  simpa only [he, eqToIso_refl, Iso.refl_symm, Iso.refl_trans] using h

/-- 元の Kan 射で正規化した、全 Hom 比較の同じ頂点成分。 -/
def pointedValueHomActionAt {K L : KanObject.{u}} (f : K ⟶ L) :
    VertexIso
      (functorVertex ((pointedSpaceFiberValueEquivalence (spaceInfinityVertex K)).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map f))
      ((pointedValueHomTransport K L).app (Opposite.op ⦋0⦌) (ULift.up (functorVertex f))) :=
  (eqToIso (congrArg SSet.HomotopyCategory.mk (pointedValueHomEvaluation_vertex f))).symm ≪≫
    (pointedValueHomActionIso K L).app (ULift.up (functorVertex f))

/-- 元の指定三角形同型・輸送の path・両端比較の同じ値が正方形を満たす。 -/
lemma pointedValueTriangle_square (s : SpaceInfinity.{u} _⦋2⦌) :
    (((spaceInfinityTriangleIso s).ulift.{u, u + 1}).precomp
        (pointedSpaceFiberValueEquivalence (spaceInfinityVertex (s.obj ⟨ULift.up 0⟩))).hom).hom ≫
      (pointedValueHomActionAt (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫
        coherentEdgeHom (SpaceInfinity.δ 0 s))).hom =
    (pointedValueHomActionAt (coherentEdgeHom (SpaceInfinity.δ 1 s))).hom ≫
      SSet.Truncated.HomotopyCategory.homMk
        (((pointedValueTriangleCoefficient s).map
          (pointedValueHomTransport (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))).toTruncated) := by
  have h := edgeIsoSquare_ofEq
    ((pointedValueTriangleCoefficient s).map
      (pointedValueHomEvaluation (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)))
    ((pointedValueTriangleCoefficient s).map
      (pointedValueHomTransport (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)))
    ((pointedValueHomActionIso (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)).app
      (ULift.up (functorVertex (coherentEdgeHom (SpaceInfinity.δ 1 s)))))
    ((pointedValueHomActionIso (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)).app
      (ULift.up (functorVertex (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫
        coherentEdgeHom (SpaceInfinity.δ 0 s)))))
    (pointedValueHomEvaluation_vertex (coherentEdgeHom (SpaceInfinity.δ 1 s)))
    (pointedValueHomEvaluation_vertex (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫
      coherentEdgeHom (SpaceInfinity.δ 0 s))) (pointedValueTriangle_naturality s)
  have he := congrArg (fun p => p ≫
    (pointedValueHomActionAt (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫
      coherentEdgeHom (SpaceInfinity.δ 0 s))).hom) (pointedValueTriangleEvaluationEdge_hom s)
  exact he.symm.trans h

/-- 同じ精密化の輸送側の辺の類を、そのまま指定同型として保持する。 -/
def pointedValueTriangleTransportIso (s : SpaceInfinity.{u} _⦋2⦌) :
    VertexIso
      ((pointedValueHomTransport (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)).app
        (Opposite.op ⦋0⦌) (ULift.up (functorVertex (coherentEdgeHom (SpaceInfinity.δ 1 s)))))
      ((pointedValueHomTransport (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)).app
        (Opposite.op ⦋0⦌) (ULift.up (functorVertex (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫
          coherentEdgeHom (SpaceInfinity.δ 0 s))))) := by
  let e := (pointedValueTriangleCoefficient s).map
    (pointedValueHomTransport (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩))
  have : IsInvertibleEdge e.toTruncated :=
    isInvertibleEdge_of_hasFinalHornFillers _ (hasFinalHornFillers_of_kanComplex _)
  exact asIso (SSet.Truncated.HomotopyCategory.homMk e.toTruncated)

/-- 元の指定三角形同型と輸送の指定同型は、同じ両端比較と同型として整合する。 -/
lemma pointedValueTriangle_isoSquare (s : SpaceInfinity.{u} _⦋2⦌) :
    ((spaceInfinityTriangleIso s).ulift.{u, u + 1}).precomp
        (pointedSpaceFiberValueEquivalence (spaceInfinityVertex (s.obj ⟨ULift.up 0⟩))).hom ≪≫
      pointedValueHomActionAt (coherentEdgeHom (SpaceInfinity.δ 2 s) ≫
        coherentEdgeHom (SpaceInfinity.δ 0 s)) =
    pointedValueHomActionAt (coherentEdgeHom (SpaceInfinity.δ 1 s)) ≪≫
      pointedValueTriangleTransportIso s := by
  apply Iso.ext
  exact pointedValueTriangle_square s

end SerrePositivity.InfinityCategories.F2
