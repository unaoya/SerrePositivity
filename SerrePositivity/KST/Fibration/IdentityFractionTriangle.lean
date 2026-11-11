module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.IdentityMarkedSpan
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.FixedFractionTriangleEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.LiftEndpoint

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
  (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W) (x : X _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1 ∈ W)

omit [Quasicategory Q] in
theorem identityInvertedSpan_inclusion :
    SSet.const ((invertedSpanMap F W hF).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityMarkedSpan W x hx)) ≫ equivalenceSpanInclusion Q =
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (F.app (Opposite.op ⦋0⦌) x) :
        (horn 2 0 : SSet.{u}) ⟶ Q)) : (Δ[0] : SSet.{u}) ⟶ _) := by
  rw [SSet.const_comp]
  congr 1
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.const x : (horn 2 0 : SSet.{u}) ⟶ X) ≫ F) = _
  rw [SSet.const_comp]

/-- 恒等 span の三角補完は、商内の同じ頂点に定値な実三角形を選べる。 -/
def identityFractionTriangle : (Δ[0] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangles F W hF x x := by
  let b := (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityMarkedSpan W x hx) : (Δ[0] : SSet.{u}) ⟶ _)
  let c := (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (F.app (Opposite.op ⦋0⦌) x) :
    (Δ[2] : SSet.{u}) ⟶ Q)) : (Δ[0] : SSet.{u}) ⟶ _)
  let e := b ≫ invertedSpanMap F W hF
  have hc : c ≫ (pre (horn 2 0).ι).app Q = e ≫ equivalenceSpanInclusion Q := by
    rw [show e = SSet.const ((invertedSpanMap F W hF).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityMarkedSpan W x hx)) from SSet.const_comp _ _,
      identityInvertedSpan_inclusion]
    rw [show c = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (F.app (Opposite.op ⦋0⦌) x) :
      (Δ[2] : SSet.{u}) ⟶ Q)) from rfl, SSet.const_comp]
    rfl
  let t : (Δ[0] : SSet.{u}) ⟶ equivalenceSpanTriangles Q := pullback.lift c e hc
  let s : (Δ[0] : SSet.{u}) ⟶ fractionTriangleDiagrams F W hF :=
    pullback.lift t b (pullback.lift_snd _ _ _)
  exact pullback.lift s (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityFixedMarkedSpan W x hx)) (by
    change s ≫ pullback.snd _ _ = _
    rw [pullback.lift_snd, SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityFixedMarkedSpan_inclusion])

omit [Quasicategory Q] in
/-- 定値三角補完は、元の指定された恒等 span の真上にある。 -/
theorem identityFractionTriangle_projection : identityFractionTriangle F W hF x hx ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangleProjection F W hF x x =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.identityFixedMarkedSpan W x hx) := pullback.lift_snd _ _ _

omit [Quasicategory Q] in
/-- 記憶した三角形そのものは、商の頂点に定値な三角形。 -/
theorem identityFractionTriangle_family : identityFractionTriangle F W hF x hx ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangleFamily F W hF x x =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (F.app (Opposite.op ⦋0⦌) x) :
        (Δ[2] : SSet.{u}) ⟶ Q)) := by
  simp only [identityFractionTriangle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangleFamily, fractionTriangleFamily,
    ← Category.assoc, pullback.lift_fst]

/-- 定値補完の第三辺は、実区間写像空間内の恒等射の点。 -/
theorem identityFractionTriangle_evaluation : identityFractionTriangle F W hF x hx ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangleEvaluation F W hF x x =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (SSet.Edge.id (F.app (Opposite.op ⦋0⦌) x))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((pre (boundary 1).ι).app Q)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary (F.app (Opposite.op ⦋0⦌) x)
      (F.app (Opposite.op ⦋0⦌) x)))
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangleEvaluation, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangleEdge, ← Category.assoc, identityFractionTriangle_family,
    SSet.const_comp, SSet.const_comp]
  congr 1
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((stdSimplex.δ (0 : Fin 3)) ≫ SSet.const _) = _
  rw [SSet.comp_const]
  congr 1
  apply SSet.yonedaEquiv.injective
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _).trans (SSet.yonedaEquiv.apply_symm_apply _).symm

end SerrePositivity.KST.Fibration
