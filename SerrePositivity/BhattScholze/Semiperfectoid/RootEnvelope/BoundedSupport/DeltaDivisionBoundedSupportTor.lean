module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.Division.DeltaDivisionBoundedSupportColimit
public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.Division.DeltaDivisionFiniteSubfamilyTor
public import SerrePositivity.HomologicalAlgebra.TorExactColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # 有界深さ有限部分族図式の実残余Tor消滅 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {σ : Type u}

private theorem coordinate_range {m : ℕ} (T : Finset σ) (s : Fin m ≃ T) (N : ℕ) :
    Set.range (deltaDivisionFiniteFamilyCoordinates (fun i => (s i : σ)) N).get =
      {z : σ × ℕ | z.1 ∈ T ∧ z.2 ≤ N} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, k, hk, he⟩ :=
      (deltaDivisionFiniteFamilyCoordinates_mem (fun i => (s i : σ)) N _).mp (List.get_mem _ i)
    rw [← he]
    exact ⟨(s j).property, hk⟩
  · rintro ⟨hz, hn⟩
    obtain ⟨j, hj⟩ := s.surjective ⟨z.1, hz⟩
    have hm : z ∈ deltaDivisionFiniteFamilyCoordinates (fun i => (s i : σ)) N :=
      (deltaDivisionFiniteFamilyCoordinates_mem (fun i => (s i : σ)) N z).mpr
        ⟨j, z.2, hn, Prod.ext (congrArg Subtype.val hj) rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hm
    exact ⟨i, hi⟩

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "P" => MvPolynomial σ A
local notation "L" => RelativeFreeDeltaRing (R := P) σ
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) a
local notation "I" => Ideal.span {(p : L), MvPolynomial.C (MvPolynomial.C d)}
local notation "ψ" => RingHom.comp (Ideal.Quotient.mk I)
  (deltaDivisionSourceMap (σ := σ) E (MvPolynomial.C d))
local notation "F" => deltaDivisionBoundedSupportModuleDiagram E r
local notation "K" => deltaDivisionEvaluationFiniteSupportIdeal E r

/-- 任意根族の有界深さ評価図式の全段は、元の実残余係数射に沿う正次数Torが零。 -/
theorem deltaRootBoundedSupportStage_tor_subsingleton
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (S : Finset (σ × ℕ)) (i : ℕ) :
    Subsingleton (((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1)).obj ((F).obj S)) := by
  classical
  let T := S.image Prod.fst
  let N := S.sup Prod.snd
  let s : Fin T.card ≃ T := (Finset.equivFin T).symm
  let cs := deltaDivisionFiniteFamilyCoordinates (fun j => (s j : σ)) N
  have hcoords : Set.range cs.get = (deltaDivisionCoordinateHull S : Set (σ × ℕ)) := by
    rw [coordinate_range T s N]
    ext z
    exact (mem_deltaDivisionCoordinateHull S z).symm
  have hK : K (deltaDivisionCoordinateHull S) =
      Ideal.span (Set.range fun j => deltaDivisionSourceGraphRelation E r (cs.get j)) := by
    change Ideal.span (deltaDivisionSourceGraphRelation E r ''
      (deltaDivisionCoordinateHull S : Set (σ × ℕ))) = _
    rw [← hcoords, ← Set.range_comp']
  let e : (F).obj S ≅
      ModuleCat.of L (DeltaDivisionSourceFiniteCoordinateQuotient E r cs.get) :=
    (Submodule.quotEquivOfEq _ _ (show (K (deltaDivisionCoordinateHull S) : Submodule L L) =
      Ideal.span (Set.range fun j => deltaDivisionSourceGraphRelation E r (cs.get j))
        from hK)).toModuleIso
  let H := (ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1)
  have ht := deltaRootFiniteSubfamilySource_tor_subsingleton
    (T : Set σ) D d a s N hpA v hv i
  have hz : IsZero (H.obj
      (ModuleCat.of L (DeltaDivisionSourceFiniteCoordinateQuotient E r cs.get))) := by
    let := ht
    exact ModuleCat.isZero_of_subsingleton _
  exact ModuleCat.subsingleton_of_isZero (hz.of_iso (H.mapIso e))

/-- この実図式のTor交換入力の下で、任意根族の全β評価環の正次数Torが零。 -/
theorem deltaRootEvaluation_tor_subsingleton_of_preservesBoundedSupportColimit
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ)
    (hpres : PreservesColimit F ((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1))) :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    Subsingleton (SerrePositivity.TorAlg ψ (i + 1) P) := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := hpres
  let H := (ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1)
  have hz : IsZero (H.obj (colimit F)) :=
    torAlg_finsetColimit_isZero_of_stages (σ × ℕ) ψ F (i + 1)
      (fun S => ModuleCat.isZero_iff_subsingleton.mpr
        (deltaRootBoundedSupportStage_tor_subsingleton D d a hpA v hv S i))
  let e : H.obj (ModuleCat.of L P) ≅ H.obj (colimit F) :=
    H.mapIso (deltaDivisionBoundedSupportColimitEvalIso E r).symm
  exact ModuleCat.subsingleton_of_isZero (hz.of_iso e)

end SerrePositivity.BhattScholze
