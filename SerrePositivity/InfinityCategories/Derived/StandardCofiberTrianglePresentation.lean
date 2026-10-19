module
public import SerrePositivity.InfinityCategories.Derived.StandardCofiberEdges
public import SerrePositivity.InfinityCategories.Derived.SuspensionShiftNaturalIso
public import SerrePositivity.InfinityCategories.Derived.HomotopyChainMapSurjectivity
public import SerrePositivity.InfinityCategories.Stable.TriangulatedInstance

/-! # Distinguished triangle の標準 cofiber 表示

概要：h D(S) の distinguished triangle は、semifree 間の鎖写像の標準列と同型。
方針：第一射を鎖写像で表し、TR3 と二成分が同型な三角形射の同型性を使う。
規約：始域の cofiber による三角構造を用いる。使われ方：D7 の全三角形の保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Pretriangulated DifferentialGraded DGNerve
open scoped Simplicial ZeroObject
variable {S : Type u} [CommRing S]

/-- Distinguished triangle は実際の標準 cofiber 三角形と同型。 -/
lemma derivedDistinguishedTriangle_standard_presentation
    (T : Triangle (derivedStableHomotopyCategory S)) (hT : T ∈ distTriang _) :
    ∃ (X Y : Semifree S) (f : X.val ⟶ Y.val),
      Nonempty (T ≅ cofiberTriangle (semifreeCofiberZeroTriangle f)
        (semifreeCofiberZeroTriangle_isCofiberSequence f)) := by
  let X := derivedStableObjectPresentation S T.obj₁
  let Y := derivedStableObjectPresentation S T.obj₂
  let eX := eqToIso (derivedStableObjectPresentation_vertex S T.obj₁)
  let eY := eqToIso (derivedStableObjectPresentation_vertex S T.obj₂)
  obtain ⟨f, hf⟩ := derivedHomotopyHom_chainMap_surjective (eX.hom ≫ T.mor₁ ≫ eY.inv)
  refine ⟨X, Y, f, ?_⟩
  let t := cofiberTriangle (semifreeCofiberZeroTriangle f)
    (semifreeCofiberZeroTriangle_isCofiberSequence f)
  have ht : t ∈ distTriang _ := cofiberTriangle_mem_cofiberDistinguishedTriangles _ _
  have he : Arrow.mk t.mor₁ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      (derivedChainMapEdge (x := Simplex.vertex X) (y := Simplex.vertex Y) f)) :=
    semifreeCofiberZeroTriangle_f_arrow f
  let ea : Arrow.mk t.mor₁ ≅ Arrow.mk T.mor₁ := eqToIso he ≪≫
    Arrow.isoMk eX eY (by
      erw [hf, Category.assoc, Category.assoc, eY.inv_hom_id, Category.comp_id]
      rfl)
  obtain ⟨e, _, _⟩ := exists_iso_of_arrow_iso t T ht hT ea
  exact ⟨e.symm⟩

end SerrePositivity.InfinityCategories
