module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGStableHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleHomotopyProperty
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleStability
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberSquareComparisonIso

/-! # K(D) の対象条件と実加群頂点の cofiber

概要：同型で閉じた三角的対象条件は、任意に選ばれた実 cofiber でも保たれる。
方針：指定辺を戻した閉加群射の標準 cone と実 cofiber を比較し、H⁰ の同型へ送る。
規約：標準 cone 以外の実普遍四角形にも適用。使われ方：有限 cell と実安定閉包の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- K(D) の対象条件を通常の h N_dg(Mod(D)) に戻す。 -/
def dgModuleHoProperty (P : ObjectProperty (_root_.SerrePositivity.DifferentialGraded.ModuleHomotopyCategory A D)) :
    ObjectProperty (hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D)) :=
  P.inverseImage (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence A (RightModule A D)).functor

/-- 実加群頂点では元の K(D) の対象条件と一致する。 -/
lemma dgModuleHoProperty_vertex (P : ObjectProperty (_root_.SerrePositivity.DifferentialGraded.ModuleHomotopyCategory A D))
    (M : _root_.SerrePositivity.DifferentialGraded.RightModule A D) :
    dgModuleHoProperty A D P (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M)) ↔
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P M := Iff.rfl

variable (P : ObjectProperty (_root_.SerrePositivity.DifferentialGraded.ModuleHomotopyCategory A D))
variable [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

/-- K(D) の同型で閉じた対象条件は、通常の h の同型でも保たれる。 -/
instance dgModuleHoProperty_isClosedUnderIsomorphisms :
    (dgModuleHoProperty A D P).IsClosedUnderIsomorphisms where
  of_iso e h := P.prop_of_iso
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence A (RightModule A D)).functor.mapIso e) h

/-- K(D) の三角的対象条件は、実零頂点を含む。 -/
instance dgModuleHoProperty_containsZero : (dgModuleHoProperty A D P).ContainsZero where
  exists_zero := ⟨SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerveZeroVertex A D),
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerveZeroVertex_isZero A D).isZeroHo, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty_zero A D P⟩

/-- 任意の実 cofiber 四角形の終点は、両入力加群の三角的対象条件を満たす。 -/
lemma dgModuleHoProperty_cofiber {M N : _root_.SerrePositivity.DifferentialGraded.RightModule A D}
    {e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N)}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare e) (hM : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P M)
    (hN : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P N) :
    dgModuleHoProperty A D P (SSet.HomotopyCategory.mk s.cofiber) := by
  let f := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e
  have he : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D f).edge = e.edge :=
    congrArg Truncated.Edge.edge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_edgeClosed A D e)
  let r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare e := {
    toZeroTriangle := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeZeroTriangle A D f
    bottom_edge := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_bottom A D f).trans
      (congrArg (fun a : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋1⦌ => SSet.yonedaEquiv.symm a) he)
    isPushout := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_isPushout A D f }
  have hr : dgModuleHoProperty A D P (SSet.HomotopyCategory.mk r.cofiber) := by
    change dgModuleHoProperty A D P
      (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f) 1 1))
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex11]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty_cone A D P f hM hN
  exact (dgModuleHoProperty A D P).prop_of_iso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSquareComparisonIso r s) hr

end SerrePositivity.InfinityCategories.Project.DerivedCategories
