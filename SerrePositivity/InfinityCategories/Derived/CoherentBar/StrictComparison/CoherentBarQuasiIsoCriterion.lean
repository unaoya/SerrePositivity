module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentHomologyColimit
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomologyBarNondegCokernel
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations

/-!
概要：coherent bar からの実 dg 射を頂点ホモロジーの余極限で擬同型判定する。
方針：C1 の実余核と指定ホモロジー余錐の余核を同じ射で比較する。
規約：strict 図式への置き換えを仮定しない。
使われ方：分解済み coherent 図式から元の filtered 余極限への比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] [IsFiltered J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    dgNerve R (RightModule R D))
  {N : ModuleCategory R D}
  (f : ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModuleUnconditional R D G) ⟶ N)

lemma dgCoherentBarMap_homologyIsIso (x : D) (p : ℤ)
    (c : Cocone (dgCoherentBarHomologyDiagram R D G x (p + 1)))
    (hc : IsColimit c)
    (he : c.pt = ((moduleEvaluation R D x).obj N).homology (p + 1))
    (hf : dgCoherentBarHomologyBarAugmentation R D G x (p + 1) ≫
        HomologicalComplex.homologyMap ((moduleEvaluation R D x).map f) (p + 1) =
      dgHomologyBarNondegAugmentation R _ c ≫ eqToHom he) :
    IsIso (HomologicalComplex.homologyMap ((moduleEvaluation R D x).map f) (p + 1)) := by
  let h₁ := dgCoherentBarHomologyBarIsCokernel R D G x p
  let h₂ := dgHomologyBarNondegAugmentationIsCokernel R _ c hc
  let e := h₁.coconePointUniqueUpToIso h₂ ≪≫ eqToIso he
  letI : Epi (dgCoherentBarHomologyBarAugmentation R D G x (p + 1)) :=
    epi_of_isColimit_cofork h₁
  have hcomp := h₁.comp_coconePointUniqueUpToIso_hom h₂ WalkingParallelPair.one
  have hmap : HomologicalComplex.homologyMap ((moduleEvaluation R D x).map f) (p + 1) =
      e.hom := by
    apply (cancel_epi (dgCoherentBarHomologyBarAugmentation R D G x (p + 1))).mp
    rw [hf]
    exact (congrArg (fun k => k ≫ eqToHom he) hcomp).symm
  rw [hmap]
  infer_instance

lemma dgCoherentBarMap_quasiIso
    (c : ∀ (x : D) (q : ℤ), Cocone (dgCoherentBarHomologyDiagram R D G x q))
    (hc : ∀ x q, IsColimit (c x q))
    (he : ∀ x q, (c x q).pt = ((moduleEvaluation R D x).obj N).homology q)
    (hf : ∀ x q, dgCoherentBarHomologyBarAugmentation R D G x q ≫
        HomologicalComplex.homologyMap ((moduleEvaluation R D x).map f) q =
      dgHomologyBarNondegAugmentation R _ (c x q) ≫ eqToHom (he x q)) :
    moduleQuasiIso R D f := by
  intro x
  apply (_root_.quasiIso_iff _).mpr
  intro q
  apply (_root_.quasiIsoAt_iff_isIso_homologyMap _ _).mpr
  have aux (p q : ℤ) (hpq : p + 1 = q)
      (c : Cocone (dgCoherentBarHomologyDiagram R D G x q)) (hc : IsColimit c)
      (he : c.pt = ((moduleEvaluation R D x).obj N).homology q)
      (hf : dgCoherentBarHomologyBarAugmentation R D G x q ≫
          HomologicalComplex.homologyMap ((moduleEvaluation R D x).map f) q =
        dgHomologyBarNondegAugmentation R _ c ≫ eqToHom he) :
      IsIso (HomologicalComplex.homologyMap ((moduleEvaluation R D x).map f) q) := by
    subst q
    exact dgCoherentBarMap_homologyIsIso R D G f x p c hc he hf
  exact aux (q - 1) q (by omega) (c x q) (hc x q) (he x q) (hf x q)

end SerrePositivity.InfinityCategories
