module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNativeFiniteCellClosure
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteCellLocalizationReflection

/-! # 元の実分母条件を主導来圏の有限 cell 条件で判定

概要：native dg nerve の実閉包・分母条件を主導来圏の指定有限 cell 条件へ接続する。
方針：代表加群が全有限 cell に属することから主導来局所化の反映を適用する。
規約：元の Hom の平坦性や局所代表の存在は不要。使われ方：有限 cell roof の実分母化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 元の native 実閉包は、主導来圏の指定有限 cell 条件で判定できる。 -/
theorem dgNative_stableVertexClosure_iff_derivedFiniteCell (P : Set D) (x : D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) ↔
      _root_.SerrePositivity.DifferentialGraded.derivedFiniteCellOver A D P ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived A D).obj
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A x))) := by
  have hx := (_root_.SerrePositivity.DifferentialGraded.moduleFiniteCellOver A D Set.univ).prop_map_obj (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy A D)
    (_root_.SerrePositivity.DifferentialGraded.moduleFiniteCell_representable A D x)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNative_stableVertexClosure_iff_finiteCell A D P x).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyFiniteCell_iff_derivedFiniteCell A D P _ hx).trans
      ((_root_.SerrePositivity.DifferentialGraded.derivedFiniteCellOver A D P).prop_iff_of_iso
        ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso A D).app _)))

/-- 実 cofiber を元の dg 対象で表示し、実分母条件を主導来圏の有限 cell 条件へ移す。 -/
theorem dgVerdierEdges_mem_iff_derivedFiniteCell (P : Set D) {a : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) _⦋1⦌}
    (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a)) (z : D) (hz : s.cofiber = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex z) :
    a ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ↔ derivedFiniteCellOver A D P
      ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived A D).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A z))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges_mem_iff A D P s, hz]
  exact dgNative_stableVertexClosure_iff_derivedFiniteCell A D P z

end SerrePositivity.InfinityCategories.Project.DerivedCategories
