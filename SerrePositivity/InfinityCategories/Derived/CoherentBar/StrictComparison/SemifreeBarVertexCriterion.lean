module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.ProjectiveBarVertexIso
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.SemifreeNativeColimit

/-!
概要：半自由 coherent 図式の射影的 bar からの擬同型で、native 余極限頂点を指定する。
方針：射影的模型での頂点比較を全写像空間同値で反映する。
規約：分解関手の余極限保存を仮定しない。
使われ方：増大射の擬同型性から strict 比較述語の頂点条件へ移る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgModuleDerivedInfinityCategory R D)

theorem dgSemifreeCoherent_barVertexComparison (N : SemifreeDGModules R D)
    (f : ForgetEnrichment.of (Complex R)
        (dgCoherentBarNormalizedModuleUnconditional R D
          (dgProjectiveBarDiagram R D (G ≫ dgNerve.map (dgSemifreeToProjective R D)))) ⟶
      ForgetEnrichment.of (Complex R) N.val)
    (hf : moduleQuasiIso R D f) :
    ∃ t : JoinCocone G, IsColimitCone t ∧ Nonempty (VertexIso t.vertex (Simplex.vertex N)) := by
  obtain ⟨t, ht⟩ := dgSemifreeCoherent_hasColimit R D G
  let q := dgNerve.map (dgSemifreeToProjective R D)
  let H := G ≫ q
  let c := dgProjectiveBarNativeCocone R D H
  have hc := dgProjectiveBarNativeCocone_isColimit R D H
  have hqt := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.equivalence_isColimitCone_iff
    (dgSemifreeToProjectiveNerve_isQCatEquivalence R D) t).mp ht
  let e₀ := colimitVertexIso (mapJoinCocone q t) c hqt hc
  let e₁ := dgProjectiveBarNativeCocone_vertexIso R D H (dgSemifreeToProjective R D |>.obj N) f hf
  have hN : q.app (Opposite.op ⦋0⦌) (Simplex.vertex N) =
      Simplex.vertex ((dgSemifreeToProjective R D).obj N) := dgFunctorNerve_vertex _ N
  let e : VertexIso (q.app (Opposite.op ⦋0⦌) t.vertex)
      (q.app (Opposite.op ⦋0⦌) (Simplex.vertex N)) :=
    e₀ ≪≫ e₁ ≪≫ eqToIso (congrArg SSet.HomotopyCategory.mk hN.symm)
  exact ⟨t, ht, ⟨(dgSemifreeToProjectiveNerve_isFullyFaithful R D).toHoFullyFaithful.preimageIso e⟩⟩

end SerrePositivity.InfinityCategories
