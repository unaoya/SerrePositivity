module
public import SerrePositivity.InfinityCategories.Derived.KappaPerfect.Closure
public import SerrePositivity.InfinityCategories.Derived.DGPerfectYonedaIdempotentCompletion
public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful

/-!
概要：同じ cone 内の perfect 安定閉包から元の実 Perf への全 Hom 比較同値。
方針：同じ加群と全 Hom を保つ dg 関手を作り、perfectCovers を頂点同型へ戻す。
規約：通常の導来同型は本質的全射性にのみ使う。使われ方：D-8 e の逆関手。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 安定閉包の同じ実加群を、元の射影的 perfect dg 模型へ送る。 -/
def dgKappaPerfectToPerf : DGFunctor R
    (DGFullSubcategory (DGKappaCone R D I)
      (dgStableClosureProperty R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)))
    (PerfectDGModule R D) where
  obj M := ⟨ForgetEnrichment.to (Complex R) M.val.val,
    I.projective M.val.val M.val.property,
    (dgKappaPerfect_stableClosure_iff R D I M.val).mp M.property⟩
  map _ _ := 𝟙 _
  map_id _ := Category.comp_id _
  map_comp _ _ _ := by
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]
    rfl

/-- 同じ全 dg Hom の恒等写像による逆向き比較。 -/
def dgKappaPerfectReverse := dgNerve.map (dgKappaPerfectToPerf R D I)

lemma dgKappaPerfectReverse_isFullyFaithful :
    IsFullyFaithful (dgKappaPerfectReverse R D I) := by
  apply dgNerve_map_isFullyFaithful_of_homIso
  intro M N
  change IsIso (𝟙 _)
  infer_instance

/-- perfectCovers の主導来同型を、元の実 Perf 内の頂点同型へ戻す。 -/
lemma dgKappaPerfectReverse_isEssentiallySurjective :
    IsEssentiallySurjective (dgKappaPerfectReverse R D I) := by
  intro z
  obtain ⟨M, rfl⟩ := Simplex.vertexEquiv.symm.surjective z
  let M₀ := ForgetEnrichment.of (Complex R) M.val
  obtain ⟨N, hN, ⟨e⟩⟩ := I.perfectCovers M₀ M.property.2
  have hp : modulePerfect R D ((moduleToDerived R D).obj N) :=
    (modulePerfect R D).prop_of_iso e.symm M.property.2
  let x : DGFullSubcategory (DGKappaCone R D I)
      (dgStableClosureProperty R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I)) :=
    ⟨⟨N, hN⟩, StableVertexClosure.of_mem ⟨⟨N, hN⟩, hp, rfl⟩⟩
  refine ⟨Simplex.vertex x, ⟨?_⟩⟩
  change VertexIso ((dgNerve.map (dgKappaPerfectToPerf R D I)).app _ (Simplex.vertex x)) _
  rw [dgFunctorNerve_vertex]
  exact (dgPerfectDerivedHoComparison R D).preimageIso
    (dgPerfectVertex_classicalIso R D ((dgKappaPerfectToPerf R D I).obj x) ≪≫ e ≪≫
      (dgPerfectVertex_classicalIso R D M).symm)

/-- 全写像空間の同値と実頂点の被覆による QCat 同値。 -/
theorem dgKappaPerfectReverse_isQCatEquivalence :
    IsQCatEquivalence (dgKappaPerfectReverse R D I) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (dgKappaPerfectReverse_isFullyFaithful R D I)
    (dgKappaPerfectReverse_isEssentiallySurjective R D I)

end SerrePositivity.InfinityCategories
