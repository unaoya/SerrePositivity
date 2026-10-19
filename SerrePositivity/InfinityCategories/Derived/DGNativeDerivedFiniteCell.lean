module
public import SerrePositivity.InfinityCategories.Derived.DGNativeFiniteCellClosure
public import SerrePositivity.InfinityCategories.Derived.DGFiniteCellLocalizationReflection

/-! # 元の実分母条件を主導来圏の有限 cell 条件で判定

概要：native dg nerve の実閉包・分母条件を主導来圏の指定有限 cell 条件へ接続する。
方針：代表加群が全有限 cell に属することから主導来局所化の反映を適用する。
規約：元の Hom の平坦性や局所代表の存在は不要。使われ方：有限 cell roof の実分母化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 元の native 実閉包は、主導来圏の指定有限 cell 条件で判定できる。 -/
theorem dgNative_stableVertexClosure_iff_derivedFiniteCell (P : Set D) (x : D) :
    StableVertexClosure (X := dgNerve A D) (Simplex.vertex '' P) (Simplex.vertex x) ↔
      derivedFiniteCellOver A D P ((moduleToDerived A D).obj
        (ForgetEnrichment.of (Complex A) (representable A x))) := by
  have hx := (moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToHomotopy A D)
    (moduleFiniteCell_representable A D x)
  exact (dgNative_stableVertexClosure_iff_finiteCell A D P x).trans
    ((dgHomotopyFiniteCell_iff_derivedFiniteCell A D P _ hx).trans
      ((derivedFiniteCellOver A D P).prop_iff_of_iso
        ((moduleToHomotopyDerivedIso A D).app _)))

/-- 実 cofiber を元の dg 対象で表示し、実分母条件を主導来圏の有限 cell 条件へ移す。 -/
theorem dgVerdierEdges_mem_iff_derivedFiniteCell (P : Set D) {a : (dgNerve A D) _⦋1⦌}
    (s : CofiberSquare (edgeOfSimplex a)) (z : D) (hz : s.cofiber = Simplex.vertex z) :
    a ∈ dgVerdierEdges A D P ↔ derivedFiniteCellOver A D P
      ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A z))) := by
  rw [dgVerdierEdges_mem_iff A D P s, hz]
  exact dgNative_stableVertexClosure_iff_derivedFiniteCell A D P z

end SerrePositivity.InfinityCategories
