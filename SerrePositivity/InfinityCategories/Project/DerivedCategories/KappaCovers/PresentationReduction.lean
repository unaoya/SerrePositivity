module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.StrictComparison

/-!
概要：実 strict 表示と D-bar の比較から、正本 covers と同じ型の結論へ接続する。
方針：固定図式を native へ移し、compact な頂点を一段の retract にして実代表へ戻す。
規約：このファイルは strict 表示の存在を証明しない。cell 構成の残りを入力に隠さず記録する。
使われ方：D-8 d の cell 構成後に使う消費側の還元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory Limits DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) [Fact κ.IsRegular]

/-- cell 構成が最終的に供給すべき、元の実加群の strict 表示のデータ。
存在定理ではなく、消費側が使うデータの型を固定する。 -/
structure DGKappaStrictRepresentativePresentation (P : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) where
  Index : Type u
  [order : PartialOrder Index]
  [filtered : IsCardinalFiltered Index κ]
  diagram : Index ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D
  cocone : Cocone diagram
  isColimit : IsColimit cocone
  iso : cocone.pt ≅ P
  stageCovers : ∀ i : Index, ∃ N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ N ∧
      Nonempty ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj N ≅ (_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).obj (diagram.obj i))

/-- 固定した strict 表示に対する covers 還元。一般の表示存在は別工程。 -/
lemma dgKappaCovers_of_strictRepresentativePresentation
    (hκ : Cardinal.aleph0 < κ) (comparison : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.DGKappaStrictFilteredColimitComparison R D κ)
    {P : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D} (p : DGKappaStrictRepresentativePresentation R D κ P)
    {y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D) _⦋0⦌}
    (eP : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (dgConeModuleDerivedVertex R D P) y)
    (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, max (u + 1) v} κ y) :
    ∃ N : ModuleCategory R D, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects R D κ N ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (dgConeModuleDerivedVertex R D N) y) := by
  letI := p.order
  letI := p.filtered
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered (κ := κ) p.Index
  obtain ⟨t, ht, ⟨et⟩⟩ := comparison p.Index p.diagram p.cocone p.isColimit
  let e := et ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertexIsoOfDerivedIso R D
    ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived R D).mapIso p.iso) ≪≫ eP
  obtain ⟨i, ⟨r⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaCompact_retract_of_nativeCellPresentation R D
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaStrictModuleDiagram R D p.diagram) t ht
    (fun i => p.diagram.obj (i.obj 0)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaStrictModuleDiagram_vertex R D p.diagram) e hy
  obtain ⟨N, hN, ⟨ei⟩⟩ := p.stageCovers (i.obj 0)
  let en := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedVertexIsoOfDerivedIso R D ei
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.dgKappaClosedProjectiveObjects_nativeRetractCovers R D hκ (Fact.out : κ.IsRegular)
    hN (r.trans (Retract.ofIso en.symm))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
