module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.UniversalCoconeHomology
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.SemifreeBarVertexCriterion

/-!
概要：半自由 coherent 図式の指定余錐のホモロジー余極限性から native 頂点を比較する。
方針：C1 の実増大の擬同型性と、射影的 bar の頂点比較を接続する。
規約：分解関手の余極限保存は入力に含めない。
使われ方：filtered strict 余極限比較の消費側。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma dgBarSemifreeToProjective_comp_inclusion :
    (dgSemifreeToProjective R D).comp (dgFullSubcategoryInclusion R (RightModule R D)
      (dgModuleProjectiveProperty R D)) =
    dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D) := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro M N
  simp only [EnrichedFunctor.comp_map, dgSemifreeToProjective, dgFullSubcategoryInclusion,
    eqToHom_refl, Category.id_comp, Category.comp_id]

lemma dgBarSemifreeAmbientDiagram_eq {I : SSet.{u}}
    (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgModuleDerivedInfinityCategory R D) :
    dgProjectiveBarDiagram R D (G ≫ dgNerve.map (dgSemifreeToProjective R D)) =
      G ≫ dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleSemifreeProperty R D)) := by
  dsimp only [dgProjectiveBarDiagram]
  rw [Category.assoc, ← dgNerve.map_comp, dgBarSemifreeToProjective_comp_inclusion]

variable {J : Type u} [PartialOrder J] [IsFiltered J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶ dgModuleDerivedInfinityCategory R D)

lemma dgSemifreeCoherent_vertexComparison_of_homologyColimit (c : JoinCocone G)
    (hc : ∀ x q, IsColimit (dgCoherentCoconeHomology R D
      (G ≫ dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleSemifreeProperty R D)))
      (mapJoinCocone (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleSemifreeProperty R D))) c) x q)) :
    ∃ t : JoinCocone G, IsColimitCone t ∧ Nonempty (VertexIso t.vertex c.vertex) := by
  let i := dgNerve.map (dgFullSubcategoryInclusion R (RightModule R D)
    (dgModuleSemifreeProperty R D))
  let A := G ≫ i
  let d := mapJoinCocone i c
  let f := dgCoherentBarCoconeUniversalMap R D A (dgCoherentBarMaurerCartan_unconditional R D A) d
  have hf := dgBarCoconeUniversal_quasiIso_of_homologyColimit R D A d hc
  let N := dgNerve.vertexEquiv R (SemifreeDGModules R D) c.vertex
  have hN : Simplex.vertex N = c.vertex := Simplex.vertexEquiv.symm_apply_apply _
  have h := dgSemifreeCoherent_barVertexComparison R D G N
  rw [dgBarSemifreeAmbientDiagram_eq] at h
  obtain ⟨t, ht, ⟨e⟩⟩ := h f hf
  exact ⟨t, ht, ⟨e ≪≫ eqToIso (congrArg SSet.HomotopyCategory.mk hN)⟩⟩

end SerrePositivity.InfinityCategories
