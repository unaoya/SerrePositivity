module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.StandardCofiberEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.EnrichedFunctors.SuspensionShiftNaturalIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.HomotopyChainMapSurjectivity
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TriangulatedInstance

/-! # Distinguished triangle の標準 cofiber 表示

概要：h D(S) の distinguished triangle は、semifree 間の鎖写像の標準列と同型。
方針：第一射を鎖写像で表し、TR3 と二成分が同型な三角形射の同型性を使う。
規約：始域の cofiber による三角構造を用いる。使われ方：D7 の全三角形の保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Pretriangulated DifferentialGraded
open scoped _root_.Simplicial ZeroObject
variable {S : Type u} [CommRing S]

/-- Distinguished triangle は実際の標準 cofiber 三角形と同型。 -/
lemma derivedDistinguishedTriangle_standard_presentation
    (T : Triangle (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyCategory S)) (hT : T ∈ distTriang _) :
    ∃ (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (f : X.val ⟶ Y.val),
      Nonempty (T ≅ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_isCofiberSequence f)) := by
  let X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableObjectPresentation S T.obj₁
  let Y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableObjectPresentation S T.obj₂
  let eX := eqToIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableObjectPresentation_vertex S T.obj₁)
  let eY := eqToIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStableObjectPresentation_vertex S T.obj₂)
  obtain ⟨f, hf⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedHomotopyHom_chainMap_surjective (eX.hom ≫ T.mor₁ ≫ eY.inv)
  refine ⟨X, Y, f, ?_⟩
  let t := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle f)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_isCofiberSequence f)
  have ht : t ∈ distTriang _ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle_mem_cofiberDistinguishedTriangles _ _
  have he : Arrow.mk t.mor₁ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) f)) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberZeroTriangle_f_arrow f
  let ea : Arrow.mk t.mor₁ ≅ Arrow.mk T.mor₁ := eqToIso he ≪≫
    Arrow.isoMk eX eY (by
      erw [hf, Category.assoc, Category.assoc, eY.inv_hom_id, Category.comp_id]
      rfl)
  obtain ⟨e, _, _⟩ := exists_iso_of_arrow_iso t T ht hT ea
  exact ⟨e.symm⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
