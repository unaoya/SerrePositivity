module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeComparisonEdge
public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentPointHom

/-!
概要：二重 coslice の同型の逆が、元の図式への制限・頂点射影・終端点制限を保つ式。
方針：元の join 結合同型の二度の uncurry と右二因子の包含を使う。
規約：任意の余錐と全パラメータに適用。使われ方：native 普遍 Hom の全余錐族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p)
local notation "q" => sliceUnderProjection p
local notation "d" => Equiv.symm (SSet.yonedaEquiv (X := sliceUnder p)) c

/-- 余錐全図式の右端点への制限は、元の coslice の射影を通る同じ頂点図式である。 -/
lemma coconeVertexDiagram_inr : joinInr K (Δ[0] : SSet.{u}) ≫ c.val = coconeVertexDiagram c := by
  rw [← sliceUnderUncurry_yoneda 0 c, sliceUnderUncurry_projection]
  rfl

/-- 元の図式への二重 coslice の制限は、左包含による同じ正規化制限そのものである。 -/
lemma coconeNestedCoslice_restriction :
    colimitCosliceRestriction c =
      normalizedCoconeRestriction c.val (joinInl K Δ[0]) c.property := by
  apply sliceUnderUncurry_injective p
  have h := colimitCosliceRestriction_uncurry c (𝟙 (sliceUnder c.val))
  have h' := normalizedCoconeRestriction_uncurry c.val (joinInl K Δ[0]) c.property
    (𝟙 (sliceUnder c.val))
  simpa only [Category.id_comp] using h.trans h'.symm

/-- 二重 coslice の逆を通してから元の図式へ制限すると、同じ coslice 内の終点になる。 -/
lemma coconeNestedCoslice_inv_restriction :
    (nestedCosliceIso c).inv ≫ colimitCosliceRestriction c = sliceUnderProjection d := by
  simp only [colimitCosliceRestriction, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- 二重 coslice の逆は、元の coslice 内の可変終点の頂点射影を厳密に保つ。 -/
lemma coconeNestedCoslice_inv_projection :
    (nestedCosliceIso c).inv ≫ sliceUnderProjection c.val = sliceUnderProjection d ≫ q := by
  rw [← colimitCosliceRestriction_projection c,
    ← Category.assoc (nestedCosliceIso c).inv, coconeNestedCoslice_inv_restriction]

/-- 二重 coslice の順方向で底へ写すと、元の全余錐族を右端点へ制限した同じ族になる。 -/
lemma coconeNestedCoslice_terminal_family {T : SSet.{u}} (f : T ⟶ sliceUnder c.val) :
    (f ≫ (nestedCosliceIso c).hom) ≫ sliceUnderPostcomp d q =
      f ≫ normalizedCoconeRestriction c.val (joinInr K Δ[0]) (coconeVertexDiagram_inr c) := by
  apply sliceUnderUncurry_injective (coconeVertexDiagram c)
  rw [nestedCosliceIso_hom_comp, sliceUnderUncurry_postcomp,
    ← sliceUnderUncurry_projection, nestedCosliceHomEquiv_doubleUncurry,
    normalizedCoconeRestriction_uncurry, ← Category.assoc, stableJoinAssociator_rightPair_inv]

/-- 二重 coslice の逆で全余錐族へ戻しても、右端点は元の底の族そのものである。 -/
lemma coconeNestedCoslice_inv_terminal_family {T : SSet.{u}} (g : T ⟶ sliceUnder d) :
    (g ≫ (nestedCosliceIso c).inv) ≫
        normalizedCoconeRestriction c.val (joinInr K Δ[0]) (coconeVertexDiagram_inr c) =
      g ≫ sliceUnderPostcomp d q := by
  have h := coconeNestedCoslice_terminal_family c (g ≫ (nestedCosliceIso c).inv)
  simpa only [Category.assoc, Iso.inv_hom_id, Category.id_comp] using h.symm

end
end SerrePositivity.InfinityCategories.HomotopyLimits
