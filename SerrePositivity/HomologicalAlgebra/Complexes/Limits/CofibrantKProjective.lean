module

public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveHomotopyInverse
public import SerrePositivity.DifferentialGraded.Complexes.TensorShift

/-!
# 実射影 cofibrant 複体の K-projective 性

概要：実射影モデルで cofibrant な非有界複体は K-projective。
方針：非輪状標的の恒等 mapping cocone へ持ち上げ、元の射影の零ホモトピーを合成。
規約：半自由表示や有界性を追加仮定にしない。
使われ方：cofibrant 始域と正規化単体のテンソル。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.CochainComplex
open _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

lemma projectiveCofibrant_isKProjective (P : Complex A)
    (hP : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ P)) : P.IsKProjective where
  nonempty_homotopy_zero {L} f hL := by
    let q := mappingCocone.fst (𝟙 L)
    have hC : (mappingCocone (𝟙 L)).Acyclic :=
      _root_.SerrePositivity.cochainAcyclic_shift ((complex_quasiIso_iff_acyclic_cone A (𝟙 L)).mp inferInstance) (-1)
    have hq : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp q := by
      rw [_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations_rlp]
      refine ⟨?_, ?_⟩
      · intro n y
        refine ⟨(mappingCocone.inl (𝟙 L)).v n n (add_zero n) y, ?_⟩
        change ((mappingCocone.inl (𝟙 L)).v n n (add_zero n) ≫ q.f n) y = y
        rw [mappingCocone.inl_v_fst_f]
        rfl
      · rw [mem_quasiIso_iff, quasiIso_iff]
        intro n
        exact (quasiIsoAt_iff_exactAt q n (hC n)).mpr (hL n)
    let sq : CommSq (0 : (HomologicalComplex.zero : Complex A) ⟶ mappingCocone (𝟙 L))
        0 q f := ⟨by simp⟩
    obtain ⟨l⟩ := ((hP q hq).sq_hasLift sq).exists_lift
    have h := (_root_.SerrePositivity.ProjectiveHomotopyInverse.coconeIdentityProjectionNullhomotopy L).compLeft l.l
    change Homotopy (l.l ≫ q) (l.l ≫ 0) at h
    exact ⟨by simpa only [l.fac_right, comp_zero] using h⟩

end SerrePositivity.ComplexLimits
