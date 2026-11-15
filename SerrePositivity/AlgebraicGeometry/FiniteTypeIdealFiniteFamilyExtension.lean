module

public import SerrePositivity.AlgebraicGeometry.FiniteTypeIdealOpenPairExtension
public import SerrePositivity.AlgebraicGeometry.FiniteTypeIdealSheafOpenUnion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
概要：指定開への制限を保ち、有限個のアフィン開で有限型な部分イデアルを選ぶ。
方針：既に扱った開の準コンパクトな和を保ち、一つのアフィン開を追加する帰納。
規約：基底は準分離。大域の準コンパクト性は、この有限族の段には不要。
使われ方：Stacks 01PF の有限アフィン被覆による有限型延長。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 指定開への制限を保ち、有限アフィン族上で有限型になる部分イデアル層を選ぶ。 -/
theorem exists_subideal_finiteType_on_finite_affine_family_extending
    {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (K : X.IdealSheafData) (W : X.Opens) (hW : IsCompact (W : Set X))
    (H : W.toScheme.IdealSheafData) (hHK : H ≤ K.comap W.ι)
    (hH : IsFiniteTypeIdealSheaf H) {ι : Type u} (U : ι → X.affineOpens)
    (t : Finset ι) :
    ∃ J : X.IdealSheafData, J ≤ K ∧ J.comap W.ι = H ∧
      ∀ i ∈ t, IsFiniteTypeIdealSheaf (J.comap (U i).1.ι) := by
  classical
  letI : CompactSpace W := isCompact_iff_compactSpace.mp hW
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨K ⊓ H.map W.ι, inf_le_left, ?_, by simp⟩
    rw [idealSheaf_comap_inf_of_openImmersion, idealSheaf_comap_map_openImmersion]
    exact inf_eq_right.mpr hHK
  | @insert i t hit ih =>
    obtain ⟨J, hJK, hJW, hJU⟩ := ih
    let F : Option t → X.Opens := fun a ↦ match a with
      | none => W
      | some a => (U a.1).1
    let T : X.Opens := ⨆ a, F a
    have hcompact : IsCompact (T : Set X) := by
      change IsCompact ((⨆ a, F a : X.Opens) : Set X)
      simp only [TopologicalSpace.Opens.coe_iSup]
      apply isCompact_iUnion
      intro a
      cases a with
      | none => exact hW
      | some a => exact (U a.1).2.isCompact
    letI : CompactSpace T := isCompact_iff_compactSpace.mp hcompact
    have hJT : IsFiniteTypeIdealSheaf (J.comap T.ι) := by
      apply isFiniteTypeIdealSheaf_comap_iSup J F
      intro a
      cases a with
      | none => change IsFiniteTypeIdealSheaf (J.comap W.ι); rwa [hJW]
      | some a => exact hJU a.1 a.2
    obtain ⟨N, hNK, hNU, hNT⟩ := exists_subideal_extending_to_affine_open
      (X.homOfLE (show T ⊓ (U i).1 ≤ T from inf_le_left))
      (X.homOfLE (show T ⊓ (U i).1 ≤ (U i).1 from inf_le_right))
      T.ι (U i).1.ι (isPullback_opens_inf T (U i).1) K (J.comap T.ι)
      (Scheme.IdealSheafData.comap_mono T.ι hJK) hJT
    have hagree (V : X.Opens) (hV : V ≤ T) : N.comap V.ι = J.comap V.ι := by
      have heq := congrArg (fun L : T.toScheme.IdealSheafData ↦
        L.comap (X.homOfLE hV)) hNT
      simpa only [← Scheme.IdealSheafData.comap_comp, X.homOfLE_ι] using heq
    refine ⟨N, hNK, (hagree W (le_iSup F none)).trans hJW, ?_⟩
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hNU
    · rw [hagree (U k).1 (le_iSup F (some ⟨k, hk⟩))]
      exact hJU k hk

end SerrePositivity.AlgebraicGeometry
