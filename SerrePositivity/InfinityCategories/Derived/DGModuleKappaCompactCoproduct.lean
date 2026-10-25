module
public import SerrePositivity.InfinityCategories.Derived.DGProjectiveCoproductCocone
public import SerrePositivity.InfinityCategories.Derived.DGModuleKappaCompactProjectiveComparison
public import SerrePositivity.InfinityCategories.Derived.DGKappaDiscretePosetShape
public import SerrePositivity.InfinityCategories.Derived.DGModuleKappaCompactCone
/-!
概要：同じ実導来加群頂点の κ-compact 性は κ 未満の直和で閉じる。
方針：射影的直和の実 coherent 余錐へ P-9 を適用し、実分解と準同型比較で戻す。
規約：正則非可算 κ と元の全 Hom の compact 性を使い、交換の追加入力を残さない。
使われ方：D-8 c5 の可算直和と c2 の球面自由基底への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet DoldKanComparison
open HomotopyLimits
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
variable {κ : Cardinal.{u}} [hreg : Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
include hreg hκ

lemma dgProjectiveCoproduct_isKappaCompact {J : Type u} (hJ : HasCardinalLT J κ)
    (M : J → ProjectiveDGModules R D)
    (hM : ∀ j, dgModuleKappaCompact R D κ (ForgetEnrichment.of (Complex R) (M j).val)) :
    dgModuleKappaCompact R D κ (∐ dgProjectiveCoproductUnderlying R D M) := by
  let c := strictNativeCocone (dgProjectiveCoproductCofan R D M)
  let e := (SSet.uliftFunctor.{max (u+1) v, u}).mapIso (dgKappaDiscretePosetNerveIso J)
  have hc := dgProjectiveCoproductCofan_isColimitCone R D M
  have hp := F2.Presentable.isKappaCompact_smallPosetColimit_universe.{u, max (u+1) v}
    hκ (DGKappaDiscretePoset J) (dgKappaDiscretePoset_hasCardinalLT J hJ)
    (c.restrict e.hom) ((isColimitCone_iff_restrict_of_isIso c e.hom).mp hc) (fun k => ?_)
  · have hv : (c.restrict e.hom).vertex = c.vertex := by
      rw [JoinCocone.vertex_eq, JoinCocone.vertex_eq]
      change SSet.yonedaEquiv (joinInr _ _ ≫ (joinMap e.hom (𝟙 _) ≫ c.val)) = _
      rw [← Category.assoc, joinInr_joinMap, Category.id_comp]
    rw [hv] at hp
    change F2.Compact.IsKappaCompact.{u, max (u+1) v} κ c.vertex at hp
    rw [strictNativeCocone_vertex] at hp
    have hv' : coherentNerveVertex (ForgetEnrichment.of (Complex R)
        (dgProjectiveCoproductObject R D M)) =
        coherentVertex (R := R) (dgProjectiveCoproductObject R D M) :=
      coherentNerveVertex_object (C := ClosedCategory R (ProjectiveDGModules R D))
        (coherentVertex (R := R) (dgProjectiveCoproductObject R D M))
    change F2.Compact.IsKappaCompact.{u, max (u+1) v} κ
      (coherentNerveVertex (ForgetEnrichment.of (Complex R)
        (dgProjectiveCoproductObject R D M))) at hp
    rw [hv'] at hp
    exact (dgModuleKappaCompact_iff_projectiveCoherentVertex R D
      (dgProjectiveCoproductObject R D M)).mpr hp
  · rcases k with ⟨k⟩
    have hk : k = ComposableArrows.mk₀ (k.obj 0) := ComposableArrows.ext₀ rfl
    rw [hk]
    change F2.Compact.IsKappaCompact.{u, max (u+1) v} κ
      ((strictCoherentDiagram (Discrete.functor (fun j =>
        ForgetEnrichment.of (Complex R) (M j)))).app _
          (ULift.up (ComposableArrows.mk₀ ⟨(k.obj 0).val⟩)))
    rw [strictCoherentDiagram_vertex]
    have hv : coherentNerveVertex (ForgetEnrichment.of (Complex R) (M (k.obj 0).val)) =
        coherentVertex (R := R) (M (k.obj 0).val) :=
      coherentNerveVertex_object (C := ClosedCategory R (ProjectiveDGModules R D))
        (coherentVertex (R := R) (M (k.obj 0).val))
    change F2.Compact.IsKappaCompact.{u, max (u+1) v} κ
      (coherentNerveVertex (ForgetEnrichment.of (Complex R) (M (k.obj 0).val)))
    rw [hv]
    exact (dgModuleKappaCompact_iff_projectiveCoherentVertex R D _).mp (hM _)

lemma dgModuleKappaCompact_coproduct {J : Type u} (hJ : HasCardinalLT J κ)
    (M : J → ModuleCategory R D) (hM : ∀ j, dgModuleKappaCompact R D κ (M j)) :
    dgModuleKappaCompact R D κ (∐ M) := by
  let P := fun j => moduleCanonicalProjectiveResolution R D (M j)
  let Q : J → ProjectiveDGModules R D := fun j =>
    ⟨ForgetEnrichment.to (Complex R) (P j).obj, (P j).projective⟩
  have hQ := dgProjectiveCoproduct_isKappaCompact R D hκ hJ Q (fun j =>
    (dgModuleKappaCompact_iff_of_quasiIso R D (P j).π (P j).quasiIso).mpr (hM j))
  exact (dgModuleKappaCompact_iff_of_quasiIso R D (Limits.Sigma.map (fun j => (P j).π))
    (module_coproductMap_quasiIso R D _ (fun j => (P j).quasiIso))).mp hQ

lemma dgModuleKappaCompact_countableCoproduct (M : ℕ → ModuleCategory R D)
    (hM : ∀ n, dgModuleKappaCompact R D κ (M n)) :
    dgModuleKappaCompact R D κ (∐ M) := by
  apply (dgModuleKappaCompact_iff_of_iso R D (Sigma.reindex Equiv.ulift M)).mp
  apply dgModuleKappaCompact_coproduct R D hκ
    (J := ULift.{u} ℕ) (M := fun n => M n.down)
  · simpa [HasCardinalLT] using hκ
  · intro n
    exact hM n.down

end SerrePositivity.InfinityCategories
