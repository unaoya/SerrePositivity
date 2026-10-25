module
public import SerrePositivity.KST.Fibration.WeakIdentityQuotientTransport
public import SerrePositivity.KST.Fibration.WeakSpanKanQuotientValueCancellation

/-!
概要：元の指定恒等点の値比較と零単体の指定値比較を、元の終点座標で照合する。
方針：元の終点等式による値座標射と、既存指定実辺の合成三角形を読む。
規約：元の二つの指定比較辺と元の恒等点を保持する。
使われ方：K-B-S の既存指定恒等点への同じ実 fiber 内の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 概要：元の q(x) 値を、同じ零単体の初頂点表示の値へ送る元の座標射。
方針：元の終点等式を同じ図式と元の Kan 対象へ写す。
規約：射は厳密な等式の射であり、別の値同値を選ばない。
使われ方：元の指定恒等値比較と零単体値比較の合成。 -/
def weakIdentityQuotientValueCoordinateMap :
    spaceInfinityObject ((weakSpanKanQuotientDiagram h x).app (Opposite.op ⦋0⦌)
      (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x))) ⟶
    spaceInfinityObject ((weakSpanKanQuotientDiagram h x).app (Opposite.op ⦋0⦌)
      (ULift.up (q.hom.app (Opposite.op ⦋0⦌)
        ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
          (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x)))))) :=
  eqToHom (congrArg spaceInfinityObject
    (congrArg ((weakSpanKanQuotientDiagram h x).app (Opposite.op ⦋0⦌))
      (congrArg ULift.up (congrArg (q.hom.app (Opposite.op ⦋0⦌))
        (transportSimplexFirstVertexMap_zeroIndex x).symm))))

/-- 概要：元の恒等点の指定値比較は、零単体の同じ指定値比較と元の座標射の合成に等しい。
方針：元の指定辺の類の合成を実三角形へ戻し、同じ三辺の Kan 射を評価する。
規約：元の全実辺を保持する。各点だけの値一致へ弱めない。
使われ方：既存指定恒等点を元の全族の値正規化で照合する。 -/
def weakIdentityQuotientValueCoordinateHomotopy :
    SSet.Homotopy (F2.spaceInfinityEdgeValue (weakIdentityQuotientValueEdge h x))
      (weakIdentityQuotientValueCoordinateMap h x ≫
        F2.spaceInfinityEdgeValue
          (weakSpanKanQuotientValueEdge h x (transportSimplexIndex (n := ⦋0⦌) x))) := by
  let c := transportSimplexIndex (n := ⦋0⦌) x
  let z := (weakSpanKanQuotientDiagram h x).app (Opposite.op ⦋0⦌)
    (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x))
  let z' := (weakSpanKanQuotientDiagram h x).app (Opposite.op ⦋0⦌)
    (ULift.up (q.hom.app (Opposite.op ⦋0⦌)
      ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌) (nerveVertex c))))
  have hz : z = z' := congrArg ((weakSpanKanQuotientDiagram h x).app (Opposite.op ⦋0⦌))
    (congrArg ULift.up (congrArg (q.hom.app (Opposite.op ⦋0⦌))
      (transportSimplexFirstVertexMap_zeroIndex x).symm))
  let e := (SSet.Edge.id z).ofEq rfl hz
  let d := weakSpanKanQuotientValueEdge h x c
  let v := weakIdentityQuotientValueEdge h x
  have hc : (coherentNerveEdge (weakIdentityQuotientValueCoordinateMap h x)).edge = e.edge := by
    have aux (w : SpaceInfinity.{u} _⦋0⦌) (hw : z = w) :
        (coherentNerveEdge (eqToHom (congrArg spaceInfinityObject hw))).edge =
          ((SSet.Edge.id z).ofEq rfl hw).edge := by
      subst w
      rw [eqToHom_refl, coherentNerveEdge_id]
      exact congrArg (fun t => (SSet.Edge.id t).edge) (coherentNerveVertex_object z)
    exact aux z' hz
  have hf : Truncated.HomotopyCategory.homMk e.toTruncated ≫
      Truncated.HomotopyCategory.homMk d.toTruncated =
        Truncated.HomotopyCategory.homMk v.toTruncated := by
    rw [homMk_edge_ofEq, SSet.Edge.toTruncated_id, Truncated.HomotopyCategory.homMk_id,
      eqToHom_refl]
    simp only [Category.id_comp]
    rw [weakSpanKanQuotientValueEdge_hom, weakIdentityQuotientValueEdge_hom]
    change (𝟙 _ ≫ eqToHom (congrArg HomotopyCategory.mk hz)) ≫
      (weakSpanKanQuotientDiagram_initialVertexIso h x c).hom =
      eqToHom (congrArg HomotopyCategory.mk hz) ≫
        (weakSpanKanQuotientDiagram_initialVertexIso h x c).hom
    rw [Category.id_comp]
  let t := Classical.choice (compStruct_nonempty_of_homMk_fac hf)
  apply F2.spaceInfinityTriangleHomotopy_of_faces _ _ _ t.simplex
  · exact t.d₂.trans hc.symm
  · exact t.d₀.trans (F2.spaceInfinityEdgeValue_edge d).symm
  · exact t.d₁.trans (F2.spaceInfinityEdgeValue_edge v).symm

end SerrePositivity.KST.Fibration
