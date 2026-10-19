module
public import SerrePositivity.InfinityCategories.Derived.DGStableHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGModuleHomotopyProperty
public import SerrePositivity.InfinityCategories.Derived.DGModuleStability
public import SerrePositivity.InfinityCategories.Stable.CofiberSquareComparisonIso

/-! # K(D) の対象条件と実加群頂点の cofiber

概要：同型で閉じた三角的対象条件は、任意に選ばれた実 cofiber でも保たれる。
方針：指定辺を戻した閉加群射の標準 cone と実 cofiber を比較し、H⁰ の同型へ送る。
規約：標準 cone 以外の実普遍四角形にも適用。使われ方：有限 cell と実安定閉包の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- K(D) の対象条件を通常の h N_dg(Mod(D)) に戻す。 -/
def dgModuleHoProperty (P : ObjectProperty (ModuleHomotopyCategory A D)) :
    ObjectProperty (hoFunctor.obj (dgModuleNerve A D)) :=
  P.inverseImage (dgStableHomotopyEquivalence A (RightModule A D)).functor

/-- 実加群頂点では元の K(D) の対象条件と一致する。 -/
lemma dgModuleHoProperty_vertex (P : ObjectProperty (ModuleHomotopyCategory A D))
    (M : RightModule A D) :
    dgModuleHoProperty A D P (SSet.HomotopyCategory.mk (Simplex.vertex M)) ↔
      dgModuleHomotopyProperty A D P M := Iff.rfl

variable (P : ObjectProperty (ModuleHomotopyCategory A D))
variable [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

/-- K(D) の同型で閉じた対象条件は、通常の h の同型でも保たれる。 -/
instance dgModuleHoProperty_isClosedUnderIsomorphisms :
    (dgModuleHoProperty A D P).IsClosedUnderIsomorphisms where
  of_iso e h := P.prop_of_iso
    ((dgStableHomotopyEquivalence A (RightModule A D)).functor.mapIso e) h

/-- K(D) の三角的対象条件は、実零頂点を含む。 -/
instance dgModuleHoProperty_containsZero : (dgModuleHoProperty A D P).ContainsZero where
  exists_zero := ⟨SSet.HomotopyCategory.mk (dgModuleNerveZeroVertex A D),
    (dgModuleNerveZeroVertex_isZero A D).isZeroHo, dgModuleHomotopyProperty_zero A D P⟩

/-- 任意の実 cofiber 四角形の終点は、両入力加群の三角的対象条件を満たす。 -/
lemma dgModuleHoProperty_cofiber {M N : RightModule A D}
    {e : Truncated.Edge (X := (truncation 2).obj (dgModuleNerve A D))
      (Simplex.vertex M) (Simplex.vertex N)}
    (s : CofiberSquare e) (hM : dgModuleHomotopyProperty A D P M)
    (hN : dgModuleHomotopyProperty A D P N) :
    dgModuleHoProperty A D P (SSet.HomotopyCategory.mk s.cofiber) := by
  let f := edgeClosed e
  have he : (dgModuleEdge A D f).edge = e.edge :=
    congrArg Truncated.Edge.edge (dgModuleEdge_edgeClosed A D e)
  let r : CofiberSquare e := {
    toZeroTriangle := dgModuleConeZeroTriangle A D f
    bottom_edge := (dgModuleConeSquare_bottom A D f).trans
      (congrArg (fun a : (dgModuleNerve A D) _⦋1⦌ => SSet.yonedaEquiv.symm a) he)
    isPushout := dgModuleConeSquare_isPushout A D f }
  have hr : dgModuleHoProperty A D P (SSet.HomotopyCategory.mk r.cofiber) := by
    change dgModuleHoProperty A D P
      (SSet.HomotopyCategory.mk (squareVertex (dgModuleConeSquare A D f) 1 1))
    rw [dgModuleConeSquare_vertex11]
    exact dgModuleHomotopyProperty_cone A D P f hM hN
  exact (dgModuleHoProperty A D P).prop_of_iso (cofiberSquareComparisonIso r s) hr

end SerrePositivity.InfinityCategories
