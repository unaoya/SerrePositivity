module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeSectionFiberSquares

/-!
概要：同じ底図式を保つ全錐の比較辺の輸送を、底の切断制限から検出する。
方針：内部 Hom の制限正方形と頂点評価正方形を順に使う。
規約：両全錐・比較辺・元の射影を保持し、選んだ頂点の切断だけを使う。
使われ方：空間値錐の一点からの極限検出と元の Yoneda の有限積保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の切断制限が同値なら、底制限の正方形の元の fiber 射も同値。 -/
lemma coneRestrictionFiber_isQCatEquivalence {K E B : SSet.{u}} (p : E ⟶ B)
    [LeftFibration p] {D : K ⟶ B} (c : JoinCone D)
    (hc : IsQCatEquivalence (leftFibrationConeRestriction p c)) :
    IsQCatEquivalence (transportSquareFiberMap
      ((ihom (join (Δ[0] : SSet.{u}) K)).map p) ((ihom K).map p)
      ((pre (joinInr Δ[0] K)).app E) ((pre (joinInr Δ[0] K)).app B)
      ((pre (joinInr Δ[0] K)).naturality p) (functorVertex c.val)) := by
  have ht : IsQCatEquivalence (eqToHom (congrArg (relativeFunctorSpace p) c.property)) :=
    (qCatEquivalenceOfIso
      (eqToIso (congrArg (relativeFunctorSpace p) c.property))).isQCatEquivalence
  apply ht.cancel_right
  rw [coneRestriction_transportSquareFiberMap]
  exact hc

/-- 頂点評価の正方形の元の fiber 射は、元の全錐での同値。 -/
lemma coneApexFiber_isQCatEquivalence {K X : SSet.{u}} [Quasicategory X]
    {D : K ⟶ X} (c : JoinCone D) (x : X _⦋0⦌) :
    IsQCatEquivalence (transportSquareFiberMap
      ((ihom (join (Δ[0] : SSet.{u}) K)).map
        (sliceUnderProjection (SSet.yonedaEquiv.symm x)))
      (sliceUnderProjection (SSet.yonedaEquiv.symm x))
      (evaluateFunctorAt (joinApexVertex K)) (evaluateFunctorAt (joinApexVertex K))
      (by rfl) (functorVertex c.val)) := by
  have ht : IsQCatEquivalence (eqToHom
      (congrArg (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)))
        (coneDiagram_apex c))) :=
    (qCatEquivalenceOfIso (eqToIso
      (congrArg (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)))
        (coneDiagram_apex c)))).isQCatEquivalence
  apply ht.cancel_right
  rw [coneApex_transportSquareFiberMap]
  exact (coneApexSectionEvaluation_homotopyEquivalence c x).isQCatEquivalence

/-- 底を保つ全錐の比較辺は、両錐の切断制限が同値なら頂点での輸送も同値。 -/
lemma coneComparisonApexTransport_isQCatEquivalence {K X : SSet.{u}} [Quasicategory X]
    {D : K ⟶ X} (c d : JoinCone D) (x : X _⦋0⦌)
    (e : SSet.Edge (functorVertex c.val) (functorVertex d.val))
    (he : IsInvertibleEdge (e.map (coneRestriction K X)))
    (hc : IsQCatEquivalence (coneSectionRestriction c x))
    (hd : IsQCatEquivalence (coneSectionRestriction d x)) :
    IsQCatEquivalence (edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm x))
      (e.map (evaluateFunctorAt (joinApexVertex K)))) := by
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm x)
  have hfull : IsQCatEquivalence
      (edgeTransport ((ihom (join (Δ[0] : SSet.{u}) K)).map p) e) := by
    apply (transportSquare_isQCatEquivalence_iff
      ((ihom (join (Δ[0] : SSet.{u}) K)).map p) ((ihom K).map p)
      ((pre (joinInr Δ[0] K)).app _) ((pre (joinInr Δ[0] K)).app X)
      ((pre (joinInr Δ[0] K)).naturality p) e
      (coneRestrictionFiber_isQCatEquivalence p c hc)
      (coneRestrictionFiber_isQCatEquivalence p d hd)).mpr
    exact edgeTransport_isQCatEquivalence_of_isInvertibleEdge ((ihom K).map p)
      (e.map (coneRestriction K X)) he
  exact (transportSquare_isQCatEquivalence_iff
    ((ihom (join (Δ[0] : SSet.{u}) K)).map p) p
    (evaluateFunctorAt (joinApexVertex K)) (evaluateFunctorAt (joinApexVertex K)) (by rfl) e
    (coneApexFiber_isQCatEquivalence c x) (coneApexFiber_isQCatEquivalence d x)).mp hfull

end SerrePositivity.InfinityCategories.HomotopyLimits
