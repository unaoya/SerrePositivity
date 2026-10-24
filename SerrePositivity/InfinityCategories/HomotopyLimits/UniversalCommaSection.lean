module

public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaSourceOppositeFibration
public import SerrePositivity.InfinityCategories.Stable.CartesianInitialBoundary
public import SerrePositivity.InfinityCategories.Stable.RelativeInitialVertices

/-!
概要：各 comma の始対象から、普遍矢印の coherent な切断を構成する。
方針：相対始対象の全部分圏の射影が自明 Kan 射であることを証明し、切断を取る。
規約：各点の選択だけを関手とみなさず、全境界の持ち上げで族を構成する。
使われ方：局所置換の各点の存在から反射関手の構成への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 各始域の comma に始対象があれば、相対始対象の射影は自明 Kan 射。 -/
lemma commaRelativeInitialProjection_trivialKanFibration {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X)
    (h : ∀ x : X _⦋0⦌, ∃ v : (unitCommaFiber G x) _⦋0⦌, IsInitialVertex v) :
    TrivialKanFibration (relativeInitialProjection (unitCommaSource G)) := by
  apply relativeInitialProjection_trivialKanFibration
  intro x
  obtain ⟨v, hv⟩ := h x
  have hi := initialBoundaryLifting_of_isInitialVertex_fiber_op (unitCommaSource G) x v hv
  let w : (relativeInitialVertices (unitCommaSource G) : SSet.{u}) _⦋0⦌ := ⟨v.val, by
    intro a
    have ha : a = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    simpa only [ha, op_id, CategoryTheory.Functor.map_id_apply] using hi⟩
  refine ⟨w, ?_⟩
  change (unitCommaSource G).app (Opposite.op ⦋0⦌) v.val = x
  exact v.property.trans (pinchedConstant_zero x)

/-- 各点の普遍矢印は、全ての頂点で相対始対象である一つの coherent な切断へまとめられる。 -/
lemma exists_unitCommaSection_of_fiberInitial {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X)
    (h : ∀ x : X _⦋0⦌, ∃ v : (unitCommaFiber G x) _⦋0⦌, IsInitialVertex v) :
    ∃ s : X ⟶ unitComma G, s ≫ unitCommaSource G = 𝟙 X ∧
      ∀ x : X _⦋0⦌, InitialBoundaryLifting (unitCommaSource G)
        (s.app (Opposite.op ⦋0⦌) x) := by
  have := commaRelativeInitialProjection_trivialKanFibration G h
  obtain ⟨r, hr⟩ := trivialKanFibration_exists_section
    (relativeInitialProjection (unitCommaSource G))
  refine ⟨r ≫ (relativeInitialVertices (unitCommaSource G)).ι, ?_, ?_⟩
  · exact hr
  · intro x
    exact fullSubcomplexOnVertices_vertex (r.app (Opposite.op ⦋0⦌) x)

end SerrePositivity.InfinityCategories.HomotopyLimits
