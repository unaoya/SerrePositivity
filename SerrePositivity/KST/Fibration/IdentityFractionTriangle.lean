module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.IdentityMarkedSpan
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FixedFractionTriangleEvaluation
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertices
public import SerrePositivity.InfinityCategories.F1.Transport.LiftEndpoint

/-! # 恒等 span の定値な三角補完を、元の選択空間に保持する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q) (W : Set (X _⦋1⦌))
  (hF : InvertsEdges F W) (x : X _⦋0⦌) (hx : PinchedHom.constant x 1 ∈ W)

omit [Quasicategory Q] in
theorem identityInvertedSpan_inclusion :
    SSet.const ((invertedSpanMap F W hF).app (Opposite.op ⦋0⦌)
      (identityMarkedSpan W x hx)) ≫ equivalenceSpanInclusion Q =
      (SSet.const (functorVertex (SSet.const (F.app (Opposite.op ⦋0⦌) x) :
        (horn 2 0 : SSet.{u}) ⟶ Q)) : (Δ[0] : SSet.{u}) ⟶ _) := by
  rw [SSet.const_comp]
  congr 1
  change functorVertex ((SSet.const x : (horn 2 0 : SSet.{u}) ⟶ X) ≫ F) = _
  rw [SSet.const_comp]

/-- 恒等 span の三角補完は、商内の同じ頂点に定値な実三角形を選べる。 -/
def identityFractionTriangle : (Δ[0] : SSet.{u}) ⟶ fixedFractionTriangles F W hF x x := by
  let b := (SSet.const (identityMarkedSpan W x hx) : (Δ[0] : SSet.{u}) ⟶ _)
  let c := (SSet.const (functorVertex (SSet.const (F.app (Opposite.op ⦋0⦌) x) :
    (Δ[2] : SSet.{u}) ⟶ Q)) : (Δ[0] : SSet.{u}) ⟶ _)
  let e := b ≫ invertedSpanMap F W hF
  have hc : c ≫ (pre (horn 2 0).ι).app Q = e ≫ equivalenceSpanInclusion Q := by
    rw [show e = SSet.const ((invertedSpanMap F W hF).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.identityMarkedSpan W x hx)) from SSet.const_comp _ _,
      identityInvertedSpan_inclusion]
    rw [show c = SSet.const (functorVertex (SSet.const (F.app (Opposite.op ⦋0⦌) x) :
      (Δ[2] : SSet.{u}) ⟶ Q)) from rfl, SSet.const_comp]
    rfl
  let t : (Δ[0] : SSet.{u}) ⟶ equivalenceSpanTriangles Q := pullback.lift c e hc
  let s : (Δ[0] : SSet.{u}) ⟶ fractionTriangleDiagrams F W hF :=
    pullback.lift t b (pullback.lift_snd _ _ _)
  exact pullback.lift s (SSet.const (identityFixedMarkedSpan W x hx)) (by
    change s ≫ pullback.snd _ _ = _
    rw [pullback.lift_snd, SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.identityFixedMarkedSpan_inclusion])

omit [Quasicategory Q] in
/-- 定値三角補完は、元の指定された恒等 span の真上にある。 -/
theorem identityFractionTriangle_projection : identityFractionTriangle F W hF x hx ≫
    fixedFractionTriangleProjection F W hF x x =
      SSet.const (identityFixedMarkedSpan W x hx) := pullback.lift_snd _ _ _

omit [Quasicategory Q] in
/-- 記憶した三角形そのものは、商の頂点に定値な三角形。 -/
theorem identityFractionTriangle_family : identityFractionTriangle F W hF x hx ≫
    fixedFractionTriangleFamily F W hF x x =
      SSet.const (functorVertex (SSet.const (F.app (Opposite.op ⦋0⦌) x) :
        (Δ[2] : SSet.{u}) ⟶ Q)) := by
  simp only [identityFractionTriangle, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleFamily, fractionTriangleFamily,
    ← Category.assoc, pullback.lift_fst]

/-- 定値補完の第三辺は、実区間写像空間内の恒等射の点。 -/
theorem identityFractionTriangle_evaluation : identityFractionTriangle F W hF x hx ≫
    fixedFractionTriangleEvaluation F W hF x x =
      SSet.const (intervalMappingVertexOfEdge (SSet.Edge.id (F.app (Opposite.op ⦋0⦌) x))) := by
  apply vertexFiber_hom_ext ((pre (boundary 1).ι).app Q)
    (functorVertex (intervalMappingBoundary (F.app (Opposite.op ⦋0⦌) x)
      (F.app (Opposite.op ⦋0⦌) x)))
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEvaluation, vertexFiberLift_ι,
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedFractionTriangleEdge, ← Category.assoc, identityFractionTriangle_family,
    SSet.const_comp, SSet.const_comp]
  congr 1
  change functorVertex ((stdSimplex.δ (0 : Fin 3)) ≫ SSet.const _) = _
  rw [SSet.comp_const]
  congr 1
  apply SSet.yonedaEquiv.injective
  exact (pinchedConstant_one _).trans (SSet.yonedaEquiv.apply_symm_apply _).symm

end SerrePositivity.KST.Fibration
