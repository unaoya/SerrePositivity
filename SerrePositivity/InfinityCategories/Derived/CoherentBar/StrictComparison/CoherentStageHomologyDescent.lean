module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerHomologyExact
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentStageHomologySupport

/-!
概要：正単体次元の段階のホモロジー類を、一段低い段階からの類へ置き換える。
方針：最高層の一次 cycle を境界で消し、実長完全列で低い段階へ持ち上げる。
規約：補正項は次の段階で零となる実連結射の像である。
使われ方：有限 support の帰納による零段階からの全射性。
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

lemma dgCoherentBarStageHomology_descent (x : D) (q : ℤ) (n : ℕ)
    (a : (dgCoherentBarNormalizedStageComplex R D G x (n + 1)).homology q) :
    ∃ b : (dgCoherentBarNormalizedStageComplex R D G x n).homology q,
      HomologicalComplex.homologyMap
        (dgCoherentBarNormalizedStageMap R D G x (show n ≤ n + 2 by omega)) q b =
      HomologicalComplex.homologyMap
        (dgCoherentBarNormalizedStageMap R D G x (Nat.le_succ (n + 1))) q a := by
  let P := HomologicalComplex.homologyMap (dgCoherentBarStageToLayer R D G x (n + 1)) q
  let δ := (dgCoherentBarLayerSequence_shortExact R D G x n).δ q (q + 1) (by simp)
  have hb : δ (P a) = 0 := by
    have h := ConcreteCategory.congr_hom
      ((dgCoherentBarLayerSequence_shortExact R D G x n).comp_δ q (q + 1) (by simp)) a
    simpa only [ModuleCat.comp_apply] using! h
  have hb' : (HomologicalComplex.homologyMap
      (dgCoherentBarStageToLayer R D G x n) (q + 1)) (δ (P a)) = 0 := by
    rw [hb, map_zero]
  obtain ⟨c, hc⟩ := dgCoherentBarLayerHomology_cycle_boundary R D G x n q (P a) hb'
  let Δ : ((moduleEvaluation R D x).obj
      (dgCoherentBarLayerGraded R D G (n + 2))).homology (q - 1) ⟶
      (dgCoherentBarNormalizedStageComplex R D G x (n + 1)).homology q :=
    (dgCoherentBarLayerSequence_shortExact R D G x (n + 1)).δ (q - 1) q
    (by change q - 1 + 1 = q; omega)
  have hP : P (a - Δ c) = 0 := by
    change P (Δ c) = P a at hc
    rw [map_sub, hc, sub_self]
  have hex := (ShortComplex.moduleCat_exact_iff _).mp
    ((dgCoherentBarLayerSequence_shortExact R D G x n).homology_exact₂ q)
  obtain ⟨b, hb⟩ := hex (a - Δ c) hP
  refine ⟨b, ?_⟩
  let i := HomologicalComplex.homologyMap
    (dgCoherentBarNormalizedStageMap R D G x (Nat.le_succ n)) q
  let j := HomologicalComplex.homologyMap
    (dgCoherentBarNormalizedStageMap R D G x (Nat.le_succ (n + 1))) q
  have hb'' : i b = a - Δ c := hb
  have hΔ : j (Δ c) = 0 := by
    have h := ConcreteCategory.congr_hom
      ((dgCoherentBarLayerSequence_shortExact R D G x (n + 1)).δ_comp (q - 1) q
        (by change q - 1 + 1 = q; omega)) c
    simpa only [ModuleCat.comp_apply] using! h
  have hi : HomologicalComplex.homologyMap
      (dgCoherentBarNormalizedStageMap R D G x (show n ≤ n + 2 by omega)) q = i ≫ j := by
    rw [← HomologicalComplex.homologyMap_comp]
    rw [dgCoherentBarStageMap_comp]
  rw [hi, ModuleCat.comp_apply, hb'', map_sub, hΔ, sub_zero]

end SerrePositivity.InfinityCategories
