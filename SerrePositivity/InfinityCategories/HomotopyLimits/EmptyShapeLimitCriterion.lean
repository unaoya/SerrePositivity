module

public import SerrePositivity.InfinityCategories.HomotopyLimits.EmptyCone
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeReindexRestrictions

/-!
概要：頂点を持たない任意の元の図式の極限性を、元の錐頂点の終対象性と照合する。
方針：頂点の空性から全次数の空性を得て、元の形状を空部分複体へ厳密に同型にする。
規約：元の全錐と頂点を保持し、標的の quasicategory 性を要求しない。
使われ方：P_Σ の空添字の有限錐を元のまま判定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 頂点を持たない元の形状は、任意の標的の空部分複体と厳密に同型。 -/
def emptyVertexShapeIso (K X : SSet.{u}) [IsEmpty (K _⦋0⦌)] :
    K ≅ ((⊥ : X.Subcomplex) : SSet.{u}) where
  hom :=
    { app _ := ↾fun s ↦ isEmptyElim (simplexLastVertex s)
      naturality := by
        intro n m a
        apply ConcreteCategory.hom_ext
        intro s
        exact isEmptyElim (simplexLastVertex s) }
  inv := Subcomplex.isInitialBot.to K
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact isEmptyElim (simplexLastVertex s)
  inv_hom_id := Subcomplex.isInitialBot.hom_ext _ _

/-- 元の空図式上の任意の全錐は、同じ元の頂点を持つ標準空錐そのもの。 -/
lemma emptyDiagramCone_eq_emptyCone {X : SSet.{u}}
    (c : JoinCone (⊥ : X.Subcomplex).ι) : c = emptyCone c.vertex := by
  apply Subtype.ext
  apply (cancel_epi (joinEmptyIso (Δ[0] : SSet.{u}) X).inv).mp
  rw [joinEmptyIso_inv]
  change joinInl Δ[0] ((⊥ : X.Subcomplex) : SSet.{u}) ≫ c.val =
    joinInl Δ[0] ((⊥ : X.Subcomplex) : SSet.{u}) ≫ (emptyCone c.vertex).val
  apply SSet.yonedaEquiv.injective
  change c.vertex = (emptyCone c.vertex).vertex
  rw [emptyCone_vertex]

/-- 頂点を持たない元の任意の図式の極限性は、同じ元の錐頂点の終対象性と同値。 -/
lemma isLimitCone_iff_terminal_of_emptyVertices {K X : SSet.{u}} [IsEmpty (K _⦋0⦌)]
    {p : K ⟶ X} (c : JoinCone p) : IsLimitCone c ↔ IsTerminalVertex c.vertex := by
  let e := emptyVertexShapeIso K X
  have hp : e.inv ≫ p = (⊥ : X.Subcomplex).ι := Subcomplex.isInitialBot.hom_ext _ _
  let d := (c.reindexIso e.symm).cast hp
  have hv : d.vertex = c.vertex := joinCone_reindexIso_vertex c e.symm
  have hd : d = emptyCone c.vertex :=
    (emptyDiagramCone_eq_emptyCone d).trans (congrArg emptyCone hv)
  constructor
  · intro hc
    have h : IsLimitCone d := ((isLimitCone_iff_reindexIso c e.symm).mp hc).cast hp
    rw [hd] at h
    exact (isLimitCone_emptyCone_iff c.vertex).mp h
  · intro hc
    have h : IsLimitCone d := hd.symm ▸ (isLimitCone_emptyCone_iff c.vertex).mpr hc
    exact (isLimitCone_iff_reindexIso c e.symm).mpr (h.cast hp.symm)

end SerrePositivity.InfinityCategories.HomotopyLimits
