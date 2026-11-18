module

public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveModel

/-!
# Trivial cofibration の鎖ホモトピー逆

概要：Hovey §2.3 の射影 trivial cofibration は鎖ホモトピー同値である。
方針：零への fibration で retraction を得て、恒等射の mapping cocone への持ち上げで差を消す。
規約：始域・終域の cofibrancy を追加仮定にせず、モデル構造は局所選択する。
使われ方：余代数区間の端点から定数関数への射の擬同型性を導く。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.ProjectiveHomotopyInverse

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.CochainComplex _root_.CochainComplex.HomComplex
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

private lemma cocone_identity_snd_boundary (Y : Complex A) :
    δ (-1) 0 (-(mappingCocone.snd (𝟙 Y))) = Cochain.ofHom (mappingCocone.fst (𝟙 Y)) := by
  rw [δ_neg, mappingCocone.snd,
    Cochain.δ_leftShift _ (-1) (-1) 0 (zero_add (-1)) 1 (by omega), mappingCone.δ_snd]
  simp only [Cochain.comp_id, Cochain.leftShift_neg, Int.negOnePow_neg,
    Int.negOnePow_one, Units.neg_smul, neg_neg]
  simp only [mappingCocone.fst, Cochain.ofHom_neg, Cocycle.cochain_ofHom_homOf_eq_coe,
    Cocycle.leftShift, Cocycle.mk_coe, one_smul]

/-- 恒等射の実 mapping cocone 射影の指定した零ホモトピー。 -/
def coconeIdentityProjectionNullhomotopy (Y : Complex A) :
    Homotopy (mappingCocone.fst (𝟙 Y)) 0 :=
  (Cochain.equivHomotopy _ _).symm
    ⟨-(mappingCocone.snd (𝟙 Y)), by simp only [_root_.SerrePositivity.ProjectiveHomotopyInverse.cocone_identity_snd_boundary,
      Cochain.ofHom_zero, add_zero]⟩

/-- 概要：射影 trivial cofibration は全次数全射に対し左持ち上げ性を持つ（Hovey §2.3）。
方針：構成済みの射影モデル構造の弱分解系を局所的に適用する。
規約：呼び出し側にモデル構造の instance を要求しない。
使われ方：retraction と鎖ホモトピーの証人を具体的に持ち上げる。 -/
lemma projectiveTrivialCofibration_llp {X Y : Complex A} (f : X ⟶ Y)
    (hf : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp f) (hq : QuasiIso f) :
    (_root_.SerrePositivity.ProjectiveModel.projectiveFibrations A).llp f := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  change (HomotopicalAlgebra.fibrations (Complex A)).llp f
  rw [HomotopicalAlgebra.fibrations_llp]
  exact ⟨hf, hq⟩

/-- 概要：射影 trivial cofibration の鎖ホモトピー逆を存在として構成する（Hovey §2.3）。
方針：retraction を得て、その差を mapping cocone の射影へ持ち上げて零ホモトピーにする。
規約：得られるホモトピー同値の順方向は元の射と等しい。
使われ方：区間の端点の前合成が Hom 複体でホモトピー同値となることを示す。 -/
lemma projectiveTrivialCofibration_homotopyEquiv {X Y : Complex A} (f : X ⟶ Y)
    (hf : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp f) (hq : QuasiIso f) :
    ∃ e : HomotopyEquiv X Y, e.hom = f := by
  have hl := _root_.SerrePositivity.ProjectiveHomotopyInverse.projectiveTrivialCofibration_llp f hf hq
  have hp₀ : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A (0 : X ⟶ (HomologicalComplex.zero : Complex A)) := by
    intro n y
    have hz : IsZero ((HomologicalComplex.zero : Complex A).X n) :=
      (HomologicalComplex.eval (ModuleCat A) (.up ℤ) n).map_isZero
        HomologicalComplex.isZero_zero
    have := ModuleCat.subsingleton_of_isZero hz
    exact ⟨0, Subsingleton.elim _ _⟩
  let s : CommSq (𝟙 X) f (0 : X ⟶ (HomologicalComplex.zero : Complex A)) 0 := ⟨by simp⟩
  obtain ⟨r⟩ := ((hl _ hp₀).sq_hasLift s).exists_lift
  let d : Y ⟶ Y := 𝟙 Y - r.l ≫ f
  let p := mappingCocone.fst (𝟙 Y)
  have hp : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A p := by
    intro n y
    refine ⟨(mappingCocone.inl (𝟙 Y)).v n n (add_zero n) y, ?_⟩
    change ((mappingCocone.inl (𝟙 Y)).v n n (add_zero n) ≫ p.f n) y = y
    rw [mappingCocone.inl_v_fst_f]
    rfl
  let t : CommSq (0 : X ⟶ mappingCocone (𝟙 Y)) f p d := ⟨by
    simp only [d, zero_comp, Preadditive.comp_sub, Category.comp_id,
      ← Category.assoc, r.fac_left, Category.id_comp, sub_self]⟩
  obtain ⟨l⟩ := ((hl p hp).sq_hasLift t).exists_lift
  have hd : Homotopy d 0 := by
    have hh : Homotopy (l.l ≫ p) (l.l ≫ 0) :=
      (_root_.SerrePositivity.ProjectiveHomotopyInverse.coconeIdentityProjectionNullhomotopy Y).compLeft l.l
    simpa only [l.fac_right, comp_zero] using hh
  have h : Homotopy (𝟙 Y) (r.l ≫ f) := by
    simpa only [d, sub_add_cancel, zero_add] using hd.add (Homotopy.refl (r.l ≫ f))
  exact ⟨{
    hom := f
    inv := r.l
    homotopyHomInvId := Homotopy.ofEq r.fac_left
    homotopyInvHomId := h.symm }, rfl⟩

end SerrePositivity.ProjectiveHomotopyInverse
