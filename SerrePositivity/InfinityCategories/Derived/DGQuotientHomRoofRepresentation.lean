module
public import SerrePositivity.InfinityCategories.Derived.DGActualRoofSpans
public import SerrePositivity.InfinityCategories.Derived.DGActualRoofWeakEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGQuotientFixedHomRoof

/-! # 商 Hom の有限図式と指定頂点の実屋根表示

概要：商 Hom の有限図式を実屋根図式で比較し、各頂点には実屋根と商屋根内の実辺を与える。
方針：実屋根比較の有限相対充填の零境界の場合を使い、実 span の相互表示に接続する。
規約：比較ホモトピーと実比較辺を保持する。使われ方：任意標的の屋根評価と商 Hom 作用の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 商 Hom の任意の有限図式は、元の実屋根図式と実比較ホモトピーを持つ。 -/
theorem dgQuotientHomFinite_actualRoofLift (P : Set D) (hP : DGQuotient.localKFlat A D P)
    (x y : D) {K : SSet.{max u v}} [K.Finite]
    (g : K ⟶ DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y)) :
    ∃ a : K ⟶ dgRoofCorrespondence A D P x y,
      Nonempty (SSet.Homotopy (a ≫ dgRoofCorrespondenceMap A D P x y)
        (g ≫ dgQuotientFixedHomRoofMap A D P x y)) :=
  HasFiniteHomotopyRelativeFillers.finiteDiagramLift
    (dgRoofCorrespondenceMap_hasFiniteHomotopyRelativeFillers A D P hP x y) _

/-- 商の指定 Hom 頂点を、実屋根と商屋根内の実比較辺で表したデータ。 -/
structure DGQuotientHomRoofRepresentation (P : Set D) (x y : D)
    (v : (DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y)) _⦋0⦌) where
  roof : DGActualRoofSpan A D P x y
  comparison : Truncated.Edge (X := (truncation 2).obj (dgQuotientRoofCorrespondence A D P x y))
    ((dgRoofCorrespondenceMap A D P x y).app (Opposite.op ⦋0⦌)
      (dgActualRoofSpanVertex A D P x y roof))
    ((dgQuotientFixedHomRoofMap A D P x y).app (Opposite.op ⦋0⦌) v)

/-- 商の任意の指定 Hom 頂点には、元の実屋根と商屋根内の実比較辺が存在する。 -/
theorem dgQuotientHomRoofRepresentation_nonempty (P : Set D)
    (hP : DGQuotient.localKFlat A D P) (x y : D)
    (v : (DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y)) _⦋0⦌) :
    Nonempty (DGQuotientHomRoofRepresentation A D P x y v) := by
  obtain ⟨a, ⟨H⟩⟩ := dgQuotientHomFinite_actualRoofLift A D P hP x y
    (SSet.yonedaEquiv.symm v)
  let k := SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{max u v}))
  let r := a.app (Opposite.op ⦋0⦌) k
  let e := (simplicialHomotopyVertexEdge H k).toTruncated
  refine ⟨{ roof := dgActualRoofVertexSpan A D P x y r
            comparison := { edge := e.edge
                            src_eq := e.src_eq.trans ?_
                            tgt_eq := e.tgt_eq.trans ?_ } }⟩
  · exact congrArg ((dgRoofCorrespondenceMap A D P x y).app (Opposite.op ⦋0⦌))
      (dgActualRoofVertexSpan_rightInverse A D P x y r).symm
  · change (dgQuotientFixedHomRoofMap A D P x y).app (Opposite.op ⦋0⦌)
      ((SSet.yonedaEquiv.symm v).app (Opposite.op ⦋0⦌) k) = _
    congr 1
    change (SSet.yonedaEquiv.symm v).app (Opposite.op ⦋0⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{max u v}))) = v
    rw [← SSet.yonedaEquiv_comp, Category.id_comp, SSet.yonedaEquiv.apply_symm_apply]

end SerrePositivity.InfinityCategories
