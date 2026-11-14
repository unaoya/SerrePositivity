module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGYonedaFiniteCellClosure
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientLocalizingEdges
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.UniverseVertexClosure

/-! # 元の native dg nerve の実閉包と有限 cell

概要：元の宇宙の dg nerve の実安定閉包は代表加群の有限 cell 条件で判定できる。
方針：実閉包の ULift 不変性と、対象持ち上げの nerve の実同型で共通宇宙の比較を降下する。
規約：対象宇宙の持ち上げを結論に残さない。使われ方：有限 cell roof の native 分母条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
/-- 持ち上げた指定頂点の nerve の実同型による像は、対象を持ち上げた指定頂点と一致。 -/
lemma dgLiftedGeneratorVertices_universe_image (P : Set D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, v, max (u + 1) v} A D).hom.app (Opposite.op ⦋0⦌) ''
      (ULift.up '' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P)) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLiftedGeneratorVertices A D P := by
  change _ '' (ULift.up '' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp A D).obj '' P)
  rw [Set.image_image, Set.image_image, Set.image_image]
  apply congrArg (fun f : D →
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, max (u + 1) v} D)) _⦋0⦌ => f '' P)
  funext x
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl

variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 元の native dg nerve の実閉包と、代表加群の有限 cell 条件の一致。 -/
theorem dgNative_stableVertexClosure_iff_finiteCell (P : Set D) (x : D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) ↔
      _root_.SerrePositivity.DifferentialGraded.homotopyFiniteCellOver A D P ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy A D).obj
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A x))) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveULift_isStable_of_pretriangulated A D
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftNerve_isStable A D
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseLiftIso.{u, v, max (u + 1) v} A D
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.hom :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableVertexClosure_image_iff e.hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence.isFullyFaithful
    (ULift.up '' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P)) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
  have hv : e.hom.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp A D).obj x) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
    rfl
  rw [dgLiftedGeneratorVertices_universe_image, hv] at h
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableVertexClosure_ulift_iff.{max u v, max (u + 1) v}
    (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)).symm.trans
      (h.symm.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLifted_stableVertexClosure_iff_finiteCell A D P x))

/-- 任意の実 cofiber 頂点を元の dg 対象で表示すると、分母条件を有限 cell で判定できる。 -/
theorem dgVerdierEdges_mem_iff_finiteCell (P : Set D) {a : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) _⦋1⦌}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a)) (z : D)
    (hz : s.cofiber = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex z) :
    a ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ↔ homotopyFiniteCellOver A D P
      ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy A D).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A z))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges_mem_iff A D P s, hz]
  exact dgNative_stableVertexClosure_iff_finiteCell A D P z

end SerrePositivity.InfinityCategories.Project.DerivedCategories
