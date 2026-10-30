module

public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.CategoryTheory.Category.Preorder

/-! # 増大する複体のホモロジー

各次数で単射な複体の増大列が一つの複体を覆うとき、そのホモロジーは
各段のホモロジーの有向極限になる。サイクルと境界の代表元を有限段に戻して示す。
ホモロジー上の遷移写像の単射性は要求しない。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory Limits HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]
    (F : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (c : Cocone F)
    (hinj : ∀ n i, Function.Injective ((c.ι.app n).f i))
    (hcover : ∀ i (x : c.pt.X i), ∃ n y, (c.ι.app n).f i y = x)

include hinj hcover in
/-- 各段の項が極限の項を覆うとき、サイクルもいずれかの段から来る。 -/
theorem cycles_exists_stage (i : ℤ) (x : c.pt.cycles i) :
    ∃ n y, cyclesMap (c.ι.app n) i y = x := by
  obtain ⟨n, y, hy⟩ := hcover i (c.pt.iCycles i x)
  let j := (ComplexShape.up ℤ).next i
  have hz : (F.obj n).d i j y = 0 := by
    apply hinj n j
    rw [map_zero]
    have he := ModuleCat.hom_ext_iff.mp ((c.ι.app n).comm i j)
    have he' := congrArg (fun f ↦ f y) he
    change c.pt.d i j ((c.ι.app n).f i y) =
      (c.ι.app n).f j ((F.obj n).d i j y) at he'
    rw [← he', hy]
    exact congrArg (fun f ↦ f.hom x) (c.pt.iCycles_d i j)
  let y' := ((F.obj n).sc i).cyclesMk y hz
  refine ⟨n, y', ?_⟩
  apply (ModuleCat.mono_iff_injective (c.pt.iCycles i)).mp inferInstance
  have he := congrArg (fun f ↦ f.hom y') (cyclesMap_i (c.ι.app n) i)
  change c.pt.iCycles i (cyclesMap (c.ι.app n) i y') =
    (c.ι.app n).f i ((F.obj n).iCycles i y') at he
  rw [he]
  have hy' : (F.obj n).iCycles i y' = y := ((F.obj n).sc i).i_cyclesMk y hz
  rwa [hy']

include hinj hcover in
/-- ホモロジー類は、いずれかの段のホモロジーから来る。 -/
theorem homology_exists_stage (i : ℤ) (x : c.pt.homology i) :
    ∃ n y, homologyMap (c.ι.app n) i y = x := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (c.pt.homologyπ i)).mp inferInstance x
  obtain ⟨n, y, rfl⟩ := cycles_exists_stage F c hinj hcover i z
  refine ⟨n, (F.obj n).homologyπ i y, ?_⟩
  exact congrArg (fun f ↦ f.hom y) (homologyπ_naturality (c.ι.app n) i)

include hinj hcover in
/-- 極限で零になるホモロジー類は、十分先の段で既に零になる。 -/
theorem homology_eventually_zero (i : ℤ) (n : ℕ) (x : (F.obj n).homology i)
    (hx : homologyMap (c.ι.app n) i x = 0) :
    ∃ (m : ℕ) (hnm : n ≤ m), homologyMap (F.map (homOfLE hnm)) i x = 0 := by
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective ((F.obj n).homologyπ i)).mp inferInstance x
  let S := c.pt.sc i
  let E := ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ
  have hE : E.Exact := E.exact_of_g_is_cokernel S.homologyIsCokernel
  have hy : c.pt.homologyπ i (cyclesMap (c.ι.app n) i y) = 0 := by
    rw [← hx]
    exact (congrArg (fun f ↦ f.hom y) (homologyπ_naturality (c.ι.app n) i)).symm
  obtain ⟨b, hb⟩ := E.moduleCat_exact_iff.mp hE (cyclesMap (c.ι.app n) i y) hy
  let j := (ComplexShape.up ℤ).prev i
  obtain ⟨m, b', hb'⟩ := hcover j b
  let k := max n m
  let f := F.map (homOfLE (le_max_left n m))
  let g := F.map (homOfLE (le_max_right n m))
  let y' := cyclesMap f i y
  let b'' := g.f j b'
  have hfn : (c.ι.app k).f i (f.f i ((F.obj n).iCycles i y)) =
      (c.ι.app n).f i ((F.obj n).iCycles i y) :=
    congrArg (fun f ↦ f.f i ((F.obj n).iCycles i y)) (c.w (homOfLE (le_max_left n m)))
  have hgm : (c.ι.app k).f j b'' = b := by
    exact (congrArg (fun f ↦ f.f j b') (c.w (homOfLE (le_max_right n m)))).trans hb'
  have hboundary : (F.obj k).toCycles j i b'' = y' := by
    apply (ModuleCat.mono_iff_injective ((F.obj k).iCycles i)).mp inferInstance
    apply hinj k i
    have h₁ := congrArg (fun f ↦ f.hom b'') ((F.obj k).toCycles_i j i)
    have h₂ := congrArg (fun f ↦ f.hom b'') ((c.ι.app k).comm j i)
    have h₃ := congrArg (fun f ↦ f.hom y) (cyclesMap_i f i)
    have h₄ := congrArg (fun f ↦ f.hom y) (cyclesMap_i (c.ι.app n) i)
    have h₅ := congrArg (fun f ↦ f.hom b) S.toCycles_i
    have hb₀ := congrArg (fun z ↦ c.pt.iCycles i z) hb
    change c.pt.iCycles i (S.toCycles b) =
      c.pt.iCycles i (cyclesMap (c.ι.app n) i y) at hb₀
    change c.pt.iCycles i (S.toCycles b) = c.pt.d j i b at h₅
    rw [h₅] at hb₀
    change (c.ι.app k).f i ((F.obj k).iCycles i ((F.obj k).toCycles j i b'')) =
      (c.ι.app k).f i ((F.obj k).iCycles i (cyclesMap f i y))
    change (F.obj k).iCycles i ((F.obj k).toCycles j i b'') = (F.obj k).d j i b'' at h₁
    change c.pt.d j i ((c.ι.app k).f j b'') = (c.ι.app k).f i ((F.obj k).d j i b'') at h₂
    change (F.obj k).iCycles i (cyclesMap f i y) = f.f i ((F.obj n).iCycles i y) at h₃
    change c.pt.iCycles i (cyclesMap (c.ι.app n) i y) =
      (c.ι.app n).f i ((F.obj n).iCycles i y) at h₄
    rw [h₁, ← h₂, hgm, h₃, hfn, ← h₄]
    exact hb₀
  refine ⟨k, le_max_left n m, ?_⟩
  have he := congrArg (fun f ↦ f.hom y) (homologyπ_naturality f i)
  change homologyMap f i ((F.obj n).homologyπ i y) = (F.obj k).homologyπ i y' at he
  rw [he, ← hboundary]
  exact congrArg (fun f ↦ f.hom b'') ((F.obj k).toCycles_comp_homologyπ j i)

/-- 複体の増大列のホモロジーに誘導される遷移写像。 -/
noncomputable def homologyStageMap (i : ℤ) (n m : ℕ) (hnm : n ≤ m) :
    (F.obj n).homology i →ₗ[R] (F.obj m).homology i :=
  (homologyMap (F.map (homOfLE hnm)) i).hom

/-- 各段からの射をまとめた、ホモロジーの有向極限からの標準写像。 -/
noncomputable def homologyDirectLimitMap (i : ℤ) :
    Module.DirectLimit (fun n ↦ (F.obj n).homology i) (homologyStageMap F i) →ₗ[R]
      c.pt.homology i :=
  Module.DirectLimit.lift R ℕ _ _ (fun n ↦ (homologyMap (c.ι.app n) i).hom)
    (fun n m hnm x ↦ by
      have he := congrArg (fun f : F.obj n ⟶ c.pt ↦ (homologyMap f i).hom x)
        (c.w (homOfLE hnm))
      rw [homologyMap_comp] at he
      exact he)

include hinj hcover in
/-- 各次数で単射かつ被覆となる増大列について、ホモロジーと有向極限は可換である。 -/
noncomputable def homologyDirectLimitEquiv (i : ℤ) :
    Module.DirectLimit (fun n ↦ (F.obj n).homology i) (homologyStageMap F i) ≃ₗ[R]
      c.pt.homology i := by
  apply LinearEquiv.ofBijective (homologyDirectLimitMap F c i)
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨n, y, rfl⟩ := Module.DirectLimit.exists_of x
    rw [homologyDirectLimitMap, Module.DirectLimit.lift_of] at hx
    obtain ⟨m, hnm, hm⟩ := homology_eventually_zero F c hinj hcover i n y hx
    rw [← Module.DirectLimit.of_f (j := m) (hij := hnm)]
    change Module.DirectLimit.of R ℕ _ (homologyStageMap F i) m
      (homologyMap (F.map (homOfLE hnm)) i y) = 0
    rw [hm, map_zero]
  · intro x
    obtain ⟨n, y, hy⟩ := homology_exists_stage F c hinj hcover i x
    refine ⟨Module.DirectLimit.of R ℕ _ (homologyStageMap F i) n y, ?_⟩
    rw [homologyDirectLimitMap, Module.DirectLimit.lift_of]
    exact hy

end SerrePositivity
