module

public import SerrePositivity.AlgebraicGeometry.ProperInductiveLevelTransport
public import SerrePositivity.AlgebraicGeometry.SchemeNilradicalReduction
public import Mathlib.Topology.NoetherianSpace

/-!
概要：Noether 基底上の固有全射には有限の帰納的レベルがある。
方針：閉像の整礎帰納と実際の被約化・2d の平坦化細分を使う。
規約：有限 Krull 次元は要求しない。原典の次元の精密な上界は主張しない。
使われ方：G3 の BS17 Lemma 2.6 の有限型模型上の存在の出口。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits TopologicalSpace
universe u

/-- Noether 基底上の BS17 Lemma 2.6：固有全射はある有限の帰納的レベルを持つ。 -/
theorem exists_properInductiveLevel_noetherian {X S : Scheme.{u}}
    [_root_.AlgebraicGeometry.IsNoetherian S] (f : X ⟶ S)
    [IsProper f] [Surjective f] [LocallyOfFinitePresentation f] :
    ∃ n : ℕ, ProperInductiveLevel n f := by
  let P : Closeds S → Prop := fun C ↦
    ∀ (Y : Scheme.{u}) (j : Y ⟶ S), IsClosedImmersion j → Set.range j = (C : Set S) →
      ∀ (X : Scheme.{u}) (f : X ⟶ Y), IsProper f → Surjective f →
        LocallyOfFinitePresentation f → ∃ n : ℕ, ProperInductiveLevel n f
  have HP : ∀ C, P C := by
    intro C
    refine wellFounded_lt.induction C ?_
    intro C IH Y j hj hjC X f hp hs hfp
    letI := hj
    letI := hp
    letI := hs
    letI := hfp
    letI : _root_.AlgebraicGeometry.IsNoetherian Y :=
      { __ := LocallyOfFiniteType.isLocallyNoetherian j,
        __ := QuasiCompact.compactSpace_of_compactSpace j }
    rcases isEmpty_or_nonempty Y with hY | hY
    · letI := hY
      letI : IsEmpty X := Function.isEmpty f
      letI : Flat f := (Flat.iff_flat_stalkMap f).mpr (fun x ↦ isEmptyElim x)
      exact ⟨0, ProperInductiveLevel.of_proper_fppf f⟩
    · letI := hY
      let Y₀ := Y.nilradical.subscheme
      let i : Y₀ ⟶ Y := Y.nilradical.subschemeι
      letI : _root_.AlgebraicGeometry.IsNoetherian Y₀ :=
        { __ := LocallyOfFiniteType.isLocallyNoetherian i,
          __ := QuasiCompact.compactSpace_of_compactSpace i }
      letI : Nonempty Y₀ := by
        obtain ⟨y⟩ := hY
        obtain ⟨x, _⟩ := i.surjective y
        exact ⟨x⟩
      let f₀ := pullback.snd f i
      obtain ⟨U, J, hU, hJU, hproper, hsurj, hIso, W, q, a,
        hq, hqflat, hqsurj, hqfp, ha⟩ :=
        exists_proper_fppf_blowup_refinement_of_proper_surjective f₀
      let r := blowupπ J
      letI : IsProper r := hproper
      letI : Surjective r := hsurj
      let Z := J.subscheme
      let z : Z ⟶ S := J.subschemeι ≫ i ≫ j
      let C' : Closeds S := ⟨Set.range z, z.isClosedEmbedding.isClosed_range⟩
      have hle : C' ≤ C := by
        change Set.range z ⊆ (C : Set S)
        rw [← hjC]
        rintro s ⟨x, rfl⟩
        exact ⟨i (J.subschemeι x), rfl⟩
      have hne : C' ≠ C := by
        obtain ⟨y, hy⟩ := hU.nonempty
        intro he
        have hmem : j (i y) ∈ (C' : Set S) := by
          rw [he, ← hjC]
          exact ⟨i y, rfl⟩
        obtain ⟨x, hx⟩ := hmem
        have hxy : J.subschemeι x = y := by
          apply i.isClosedEmbedding.injective
          apply j.isClosedEmbedding.injective
          exact hx
        have hyJ : (J.support : Set Y₀) y := by
          rw [← J.range_subschemeι]
          exact ⟨x, hxy⟩
        have hynJ : y ∉ J.support := by
          change y ∈ centerComplement J
          rwa [hJU]
        exact hynJ hyJ
      have hlt : C' < C := lt_of_le_of_ne hle hne
      let e := pullback.snd r J.subschemeι
      obtain ⟨n, hn⟩ := IH C' hlt Z z inferInstance rfl _ e
        (inferInstance : IsProper e) (inferInstance : Surjective e)
        (inferInstance : LocallyOfFinitePresentation e)
      have hIsoJ : IsIso (r ∣_ centerComplement J) := by
        rwa [hJU]
      have hlevel : ProperInductiveLevel (n + 1) f₀ := by
        refine ⟨W, blowup J, Y₀, 𝟙 Y₀, r, q, a, J,
          inferInstance, inferInstance, inferInstance, hproper, hsurj, inferInstance,
          inferInstance, hIsoJ, hn, hq, hqflat, hqsurj, hqfp, ?_⟩
        simpa only [Category.comp_id] using ha
      exact ⟨n + 1, ProperInductiveLevel.of_nilimmersion_baseChange f i hlevel⟩
  exact HP ⊤ S (𝟙 S) inferInstance (by simp) X f inferInstance inferInstance inferInstance

end SerrePositivity.AlgebraicGeometry
