module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.Division.DeltaPDivisionSequentialKoszul

/-! # 通常有限関係商の逐次極限としてのraw δ包

実δ閉包が有限関係イデアルの上限である既存定理を使う。
実標準商射で与えられる余錐の普遍性を、共通の自由環の加群圏で証明する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "I₀" => deltaDivisionFiniteRelationIdeal D (p : A) a₀
local notation "J₀" => DeltaStructure.deltaClosure (relativeFreeDeltaStructure σ D)
  (deltaDivisionRelationIdeal (p : A) a₀)
local notation "Q₀" => deltaPDivisionFiniteQuotientModuleDiagram (σ := σ) D y

omit [Unique σ] in
private theorem finite_le_raw (N : ℕ) : I₀ N ≤ J₀ := by
  rw [deltaDivision_deltaClosure_eq_iSup_finiteRelations]
  exact le_iSup _ N

/-- 有限通常商からraw δ包への標準L線形射。 -/
def deltaPDivisionFiniteQuotientToRaw (N : ℕ) :
    (L₀ ⧸ I₀ N) →ₗ[L₀] DeltaAdjoinDivision D (p : A) a₀ :=
  Submodule.mapQ (I₀ N) J₀ LinearMap.id (by exact finite_le_raw D y N)

omit [Unique σ] in
/-- raw δ包への射は元の自由環の標準商元を保つ。 -/
theorem deltaPDivisionFiniteQuotientToRaw_mk (N : ℕ) (r : L₀) :
    deltaPDivisionFiniteQuotientToRaw D y N (Ideal.Quotient.mk (I₀ N) r) =
      Ideal.Quotient.mk J₀ r :=
  Submodule.mapQ_apply _ _ _ r

/-- 実有限商図式からraw δ包への標準余錐。 -/
def deltaPDivisionFiniteQuotientRawCocone : Cocone Q₀ where
  pt := ModuleCat.of L₀ (DeltaAdjoinDivision D (p : A) a₀)
  ι := NatTrans.ofSequence (fun N => ModuleCat.ofHom (deltaPDivisionFiniteQuotientToRaw D y N))
    (by
      intro N
      rw [deltaPDivisionFiniteQuotientModuleDiagram_map_succ]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      change deltaPDivisionFiniteQuotientToRaw D y (N + 1)
        (deltaPDivisionFiniteQuotientTransition D y N (Ideal.Quotient.mk (I₀ N) r)) =
        deltaPDivisionFiniteQuotientToRaw D y N (Ideal.Quotient.mk (I₀ N) r)
      rw [deltaPDivisionFiniteQuotientTransition_mk,
        deltaPDivisionFiniteQuotientToRaw_mk, deltaPDivisionFiniteQuotientToRaw_mk])

omit [Unique σ] in
private theorem cocone_mk_independent (c : Cocone Q₀) (N : ℕ) (r : L₀) :
    (c.ι.app N).hom (Ideal.Quotient.mk (I₀ N) r) =
      (c.ι.app 0).hom (Ideal.Quotient.mk (I₀ 0) r) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      have h := congrArg (fun f => f.hom (Ideal.Quotient.mk (I₀ N) r))
        (c.w (homOfLE (Nat.le_succ N)))
      rw [deltaPDivisionFiniteQuotientModuleDiagram_map_succ] at h
      change (c.ι.app (N + 1)).hom
        (deltaPDivisionFiniteQuotientTransition D y N (Ideal.Quotient.mk (I₀ N) r)) = _ at h
      rw [deltaPDivisionFiniteQuotientTransition_mk] at h
      exact h.trans ih

omit [Unique σ] in
private theorem cocone_base_ker (c : Cocone Q₀) :
    J₀ ≤ LinearMap.ker ((c.ι.app 0).hom.comp (Submodule.mkQ (I₀ 0))) := by
  rw [deltaDivision_deltaClosure_eq_iSup_finiteRelations]
  apply iSup_le
  intro N r hr
  change (c.ι.app 0).hom (Ideal.Quotient.mk (I₀ 0) r) = 0
  rw [← cocone_mk_independent D y c N r,
    Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

/-- raw δ包の標準余錐は、実通常有限商図式のcolimitである。 -/
def deltaPDivisionFiniteQuotientRawIsColimit :
    IsColimit (deltaPDivisionFiniteQuotientRawCocone (σ := σ) D y) where
  desc c := ModuleCat.ofHom
    (Submodule.liftQ J₀ ((c.ι.app 0).hom.comp (Submodule.mkQ (I₀ 0)))
      (by exact cocone_base_ker D y c))
  fac c N := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    change Submodule.liftQ J₀ ((c.ι.app 0).hom.comp (Submodule.mkQ (I₀ 0)))
      (cocone_base_ker D y c)
      (deltaPDivisionFiniteQuotientToRaw D y N (Ideal.Quotient.mk (I₀ N) r)) = _
    rw [deltaPDivisionFiniteQuotientToRaw_mk]
    exact (cocone_mk_independent D y c N r).symm
  uniq c f hf := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    have h := congrArg (fun g => g.hom (Ideal.Quotient.mk (I₀ 0) r)) (hf 0)
    change f.hom (deltaPDivisionFiniteQuotientToRaw D y 0 (Ideal.Quotient.mk (I₀ 0) r)) = _ at h
    rw [deltaPDivisionFiniteQuotientToRaw_mk] at h
    exact h

/-- 実有限通常商の圏論的colimitとraw δ包の標準比較同型。 -/
def deltaPDivisionFiniteQuotientColimitRawIso :
    colimit Q₀ ≅ ModuleCat.of L₀ (DeltaAdjoinDivision D (p : A) a₀) :=
  (colimit.isColimit Q₀).coconePointUniqueUpToIso (deltaPDivisionFiniteQuotientRawIsColimit D y)

omit [Unique σ] in
/-- 標準比較同型は、各有限通常商のraw δ包への標準射と一致する。 -/
theorem deltaPDivisionFiniteQuotientColimitRawIso_ι (N : ℕ) :
    colimit.ι Q₀ N ≫ (deltaPDivisionFiniteQuotientColimitRawIso D y).hom =
      ModuleCat.ofHom (deltaPDivisionFiniteQuotientToRaw D y N) := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit Q₀)
    (deltaPDivisionFiniteQuotientRawIsColimit D y) N

/-- 実無限KoszulモデルのH⁰は、raw δ包にL線形同型となる。 -/
def deltaPDivisionSequentialKoszulH0RawIso :
    (colimit (deltaPDivisionFiniteKoszulDiagram (σ := σ) D y)).homology 0 ≅
      ModuleCat.of L₀ (DeltaAdjoinDivision D (p : A) a₀) :=
  deltaPDivisionSequentialKoszulH0ColimitIso D y ≪≫ deltaPDivisionFiniteQuotientColimitRawIso D y

end SerrePositivity.BhattScholze
