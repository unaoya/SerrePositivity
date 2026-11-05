module
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.StrictComparison

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) [Fact κ.IsRegular]

/-- cell 構成が最終的に供給すべき、元の実加群の strict 表示のデータ。
存在定理ではなく、消費側が使うデータの型を固定する。 -/
structure DGKappaStrictRepresentativePresentation (P : ModuleCategory R D) where
  Index : Type u
  [order : PartialOrder Index]
  [filtered : IsCardinalFiltered Index κ]
  diagram : Index ⥤ ModuleCategory R D
  cocone : Cocone diagram
  isColimit : IsColimit cocone
  iso : cocone.pt ≅ P
  stageCovers : ∀ i : Index, ∃ N : ModuleCategory R D,
    dgKappaClosedProjectiveObjects R D κ N ∧
      Nonempty ((moduleToDerived R D).obj N ≅ (moduleToDerived R D).obj (diagram.obj i))

/-- 固定した strict 表示に対する covers 還元。一般の表示存在は別工程。 -/
lemma dgKappaCovers_of_strictRepresentativePresentation
    (hκ : Cardinal.aleph0 < κ) (comparison : DGKappaStrictFilteredColimitComparison R D κ)
    {P : ModuleCategory R D} (p : DGKappaStrictRepresentativePresentation R D κ P)
    {y : (dgModuleDerivedInfinityCategory R D) _⦋0⦌}
    (eP : VertexIso (dgConeModuleDerivedVertex R D P) y)
    (hy : F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ y) :
    ∃ N : ModuleCategory R D, dgKappaClosedProjectiveObjects R D κ N ∧
      Nonempty (VertexIso (dgConeModuleDerivedVertex R D N) y) := by
  letI := p.order
  letI := p.filtered
  letI := F2.Ind.isKappaFiltered_nerve_of_cardinalFiltered (κ := κ) p.Index
  obtain ⟨t, ht, ⟨et⟩⟩ := comparison p.Index p.diagram p.cocone p.isColimit
  let e := et ≪≫ dgConeModuleDerivedVertexIsoOfDerivedIso R D
    ((moduleToDerived R D).mapIso p.iso) ≪≫ eP
  obtain ⟨i, ⟨r⟩⟩ := dgKappaCompact_retract_of_nativeCellPresentation R D
    (dgKappaStrictModuleDiagram R D p.diagram) t ht
    (fun i => p.diagram.obj (i.obj 0)) (dgKappaStrictModuleDiagram_vertex R D p.diagram) e hy
  obtain ⟨N, hN, ⟨ei⟩⟩ := p.stageCovers (i.obj 0)
  let en := dgConeModuleDerivedVertexIsoOfDerivedIso R D ei
  exact dgKappaClosedProjectiveObjects_nativeRetractCovers R D hκ (Fact.out : κ.IsRegular)
    hN (r.trans (Retract.ofIso en.symm))

end SerrePositivity.InfinityCategories
