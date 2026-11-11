module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.ResolutionDiagram

/-!
概要：元の実導来 ∞ 圏の全 κ-compact 頂点を、同じ選択代表系で被覆する。
方針：標準 resolution の実 κ-filtered 表示を native へ送り、compact retract と swindle を使う。
規約：唯一残す比較引数は D-bar の native/strict 余極限比較。cell 表示の存在はここで供給する。
使われ方：`DGKappaConeInput.covers` と同じ型の D 側供給。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) [Fact κ.IsRegular]

lemma dgKappaCone_covers_of_strictFilteredColimitComparison
    (hκ : Cardinal.aleph0 < κ) (comparison : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaStrictFilteredColimitComparison R D κ)
    (y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) _⦋0⦌)
    (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, max (u + 1) v} κ y) :
    ∃ N : ModuleCategory R D, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ N ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (dgConeModuleDerivedVertex R D N) y) := by
  obtain ⟨P, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective y
  let P₀ := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) P.val
  let H := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedHoComparison R D
  have eP : H.obj (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P)) ≅
      (_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj P₀ := (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R D).app P₀
  let e₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (dgConeModuleDerivedVertex R D P₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P) :=
    H.preimageIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertex_classicalIso R D P₀ ≪≫ eP.symm)
  let eR := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertexIsoOfDerivedIso R D
    (_root_.SerrePositivity.DifferentialGraded.moduleDerivedIso R D (_root_.SerrePositivity.DifferentialGraded.moduleResolutionCandidateπ R D P₀)
      (_root_.SerrePositivity.DifferentialGraded.moduleResolutionCandidateπ_quasiIso R D P₀))
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCovers_of_strictRepresentativePresentation R D κ hκ comparison
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaResolutionStrictRepresentativePresentation R D P₀ κ hκ) (eR ≪≫ e₀) hy

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
