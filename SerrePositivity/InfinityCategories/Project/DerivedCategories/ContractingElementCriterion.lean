module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ContractingZeroVertex
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyCategoryBridge

/-! # dg nerve の零対象と収縮元の同値

概要：dg 対象の頂点の零対象性は、次数 −1 の収縮元の存在と同値。
方針：終対象性から h の恒等辺と零辺を同定し、辺ホモトピーの境界判定を使う。
規約：逆向きは実全境界充填で証明済み。使われ方：β3 の零化条件の判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 終対象となる dg 頂点の対象には、実際の次数 −1 の収縮元が存在する。 -/
lemma dgNerve_exists_contractingElement_of_isTerminalVertex (x : D)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) :
    ∃ h : _root_.SerrePositivity.DifferentialGraded.GradedHom A x x (-1),
      (_root_.SerrePositivity.DifferentialGraded.homObject A D x x).d (-1) 0 h = (_root_.SerrePositivity.DifferentialGraded.unitElement A x).val := by
  let e := Truncated.Edge.id (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)
  let z := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle (A := A) (D := D) (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) 0
  have he : Truncated.HomotopyCategory.homMk e = Truncated.HomotopyCategory.homMk z :=
    hx.isTerminalHo.hom_ext _ _
  have h₂ := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D)).map he
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory, Truncated.HomotopyCategory.lift_map_homMk] at h₂
  have hh : Truncated.HomotopicL e z := Quotient.exact h₂
  obtain ⟨h, dh⟩ := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.homotopicL_iff_exists e z).1 hh
  dsimp only [e, z] at dh
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeCycle_id, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle_edgeOfCycle] at dh
  change (_root_.SerrePositivity.DifferentialGraded.homObject A D x x).d (-1) 0 h = (_root_.SerrePositivity.DifferentialGraded.unitElement A x).val - 0 at dh
  exact ⟨h, by simpa only [sub_zero] using dh⟩

/-- dg nerve の零対象性は dg 対象の収縮元の存在と同値。 -/
lemma dgNerve_isZeroVertex_iff_contractingElement (x : D) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) ↔
      ∃ h : _root_.SerrePositivity.DifferentialGraded.GradedHom A x x (-1),
        (_root_.SerrePositivity.DifferentialGraded.homObject A D x x).d (-1) 0 h = (_root_.SerrePositivity.DifferentialGraded.unitElement A x).val := by
  constructor
  · intro hx
    exact dgNerve_exists_contractingElement_of_isTerminalVertex x hx.2
  · rintro ⟨h, dh⟩
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_contractingElement_isZeroVertex x h dh

/-- dg nerve の終頂点は零頂点でもある。 -/
lemma dgNerve_isZeroVertex_of_isTerminalVertex (x : D)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) :=
  (dgNerve_isZeroVertex_iff_contractingElement x).2
    (dgNerve_exists_contractingElement_of_isTerminalVertex x hx)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
