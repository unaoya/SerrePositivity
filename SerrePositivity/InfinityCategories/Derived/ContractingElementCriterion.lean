module
public import SerrePositivity.InfinityCategories.Derived.ContractingZeroVertex
public import SerrePositivity.InfinityCategories.Core.HomotopyCategoryBridge

/-! # dg nerve の零対象と収縮元の同値

概要：dg 対象の頂点の零対象性は、次数 −1 の収縮元の存在と同値。
方針：終対象性から h の恒等辺と零辺を同定し、辺ホモトピーの境界判定を使う。
規約：逆向きは実全境界充填で証明済み。使われ方：β3 の零化条件の判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 終対象となる dg 頂点の対象には、実際の次数 −1 の収縮元が存在する。 -/
lemma dgNerve_exists_contractingElement_of_isTerminalVertex (x : D)
    (hx : IsTerminalVertex (X := dgNerve A D) (Simplex.vertex x)) :
    ∃ h : GradedHom A x x (-1),
      (homObject A D x x).d (-1) 0 h = (unitElement A x).val := by
  let e := Truncated.Edge.id (X := twoTruncation A D) (Simplex.vertex x)
  let z := edgeOfCycle (A := A) (D := D) (x := Simplex.vertex x) (y := Simplex.vertex x) 0
  have he : Truncated.HomotopyCategory.homMk e = Truncated.HomotopyCategory.homMk z :=
    hx.isTerminalHo.hom_ext _ _
  have h₂ := congrArg (pathToEdgeHomotopyCategory (twoTruncation A D)).map he
  simp only [pathToEdgeHomotopyCategory, Truncated.HomotopyCategory.lift_map_homMk] at h₂
  have hh : Truncated.HomotopicL e z := Quotient.exact h₂
  obtain ⟨h, dh⟩ := (homotopicL_iff_exists e z).1 hh
  dsimp only [e, z] at dh
  rw [edgeCycle_id, edgeCycle_edgeOfCycle] at dh
  change (homObject A D x x).d (-1) 0 h = (unitElement A x).val - 0 at dh
  exact ⟨h, by simpa only [sub_zero] using dh⟩

/-- dg nerve の零対象性は dg 対象の収縮元の存在と同値。 -/
lemma dgNerve_isZeroVertex_iff_contractingElement (x : D) :
    IsZeroVertex (X := dgNerve A D) (Simplex.vertex x) ↔
      ∃ h : GradedHom A x x (-1),
        (homObject A D x x).d (-1) 0 h = (unitElement A x).val := by
  constructor
  · intro hx
    exact dgNerve_exists_contractingElement_of_isTerminalVertex x hx.2
  · rintro ⟨h, dh⟩
    exact dgNerve_contractingElement_isZeroVertex x h dh

/-- dg nerve の終頂点は零頂点でもある。 -/
lemma dgNerve_isZeroVertex_of_isTerminalVertex (x : D)
    (hx : IsTerminalVertex (X := dgNerve A D) (Simplex.vertex x)) :
    IsZeroVertex (X := dgNerve A D) (Simplex.vertex x) :=
  (dgNerve_isZeroVertex_iff_contractingElement x).2
    (dgNerve_exists_contractingElement_of_isTerminalVertex x hx)

end SerrePositivity.InfinityCategories
