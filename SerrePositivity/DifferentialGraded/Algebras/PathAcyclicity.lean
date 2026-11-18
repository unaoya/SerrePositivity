module

public import SerrePositivity.DifferentialGraded.Algebras.PathInput
public import SerrePositivity.HomotopicalAlgebra.Transfer.Right

/-!
# AW path の持ち上げによる自由 cell の acyclicity

概要：全射に左持ち上げ性を持つ実 dg 代数射は底で擬同型。
方針：終対象への持ち上げで retraction、二端点への持ち上げで逆合成を比較する。
規約：始域の cofibrancy と代数のモデル構造を仮定しない。
使われ方：同じ自由 J-cell 族の acyclicity と右転送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DGAlgebra
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded
variable {R : Type u} [CommRing R] (d : _root_.SerrePositivity.DGAlgebra.AWPathInput R)

attribute [local instance] _root_.SerrePositivity.DGAlgebra.hasBinaryProducts _root_.SerrePositivity.DGAlgebra.hasTerminal

/-- 概要：全射への左持ち上げ性から retraction と同じ AW path を得る。
方針：終対象と二端点評価に順に持ち上げる。
規約：元の代数射と同じ厳密な三角形を保持する。
使われ方：底の射の擬同型性。 -/
lemma exists_retraction_path {X Y : Mon (Complex R)} (f : X ⟶ Y)
    (hf : ((_root_.SerrePositivity.ProjectiveModel.projectiveFibrations R).inverseImage (Mon.forget (Complex R))).llp f) :
    ∃ r : Y ⟶ X, f ≫ r = 𝟙 X ∧ ∃ h : Y ⟶ (d.path Y).P,
      h ≫ (d.path Y).p₀ = r ≫ f ∧ h ≫ (d.path Y).p₁ = 𝟙 Y := by
  let s : CommSq (𝟙 X) f (terminal.from X) (terminal.from Y) := ⟨by simp⟩
  obtain ⟨r⟩ :=
    ((hf (terminal.from X) (_root_.SerrePositivity.DGAlgebra.terminalFrom_projectiveFibration R X)).sq_hasLift s).exists_lift
  have hr : f ≫ r.l = 𝟙 X := r.fac_left
  let Q := d.path Y
  let pair : Y ⟶ Y ⨯ Y := prod.lift (r.l ≫ f) (𝟙 Y)
  let t : CommSq (f ≫ Q.ι) f Q.p pair := ⟨by
    apply prod.hom_ext
    · simp only [Category.assoc, PrepathObject.p_fst, Q.ι_p₀,
        Category.comp_id, pair, prod.lift_fst]
      rw [← Category.assoc, hr, Category.id_comp]
    · simp only [Category.assoc, PrepathObject.p_snd, Q.ι_p₁,
        Category.comp_id, pair, prod.lift_snd]⟩
  obtain ⟨h⟩ := ((hf Q.p (d.pair_fibration Y)).sq_hasLift t).exists_lift
  refine ⟨r.l, hr, h.l, ?_, ?_⟩
  · have hh := congrArg (fun a => a ≫ prod.fst) h.fac_right
    simpa only [Category.assoc, PrepathObject.p_fst, pair, prod.lift_fst] using hh
  · have hh := congrArg (fun a => a ≫ prod.snd) h.fac_right
    simpa only [Category.assoc, PrepathObject.p_snd, pair, prod.lift_snd] using hh

include d in
/-- 概要：全射への左持ち上げ性を持つ代数射は底で擬同型。
方針：両端点の擬同型性と retraction の二つの三角形を使う。
規約：モデル構造の存在を先取りしない。
使われ方：自由 J の生成左類の acyclicity。 -/
lemma fibrations_llp_quasiIso {X Y : Mon (Complex R)} (f : X ⟶ Y)
    (hf : ((_root_.SerrePositivity.ProjectiveModel.projectiveFibrations R).inverseImage (Mon.forget (Complex R))).llp f) :
    QuasiIso f.hom := by
  obtain ⟨r, hr, h, h₀, h₁⟩ := _root_.SerrePositivity.DGAlgebra.exists_retraction_path d f hf
  have hr' : f.hom ≫ r.hom = 𝟙 X.X := congrArg Mon.Hom.hom hr
  have h₀' : h.hom ≫ ((d.path Y).p₀).hom = r.hom ≫ f.hom := congrArg Mon.Hom.hom h₀
  have h₁' : h.hom ≫ ((d.path Y).p₁).hom = 𝟙 Y.X := congrArg Mon.Hom.hom h₁
  have := d.second_quasiIso Y
  have : QuasiIso (h.hom ≫ ((d.path Y).p₁).hom) := by rw [h₁']; infer_instance
  have : QuasiIso h.hom := quasiIso_of_comp_right h.hom ((d.path Y).p₁).hom
  have := d.first_quasiIso Y
  have : QuasiIso (r.hom ≫ f.hom) := by rw [← h₀']; infer_instance
  apply quasiIso_of_retractArrow (f' := r.hom ≫ f.hom)
  refine {
    i := Arrow.homMk f.hom (𝟙 _) (by
      change f.hom ≫ (r.hom ≫ f.hom) = f.hom ≫ 𝟙 _
      rw [← Category.assoc, hr', Category.id_comp, Category.comp_id])
    r := Arrow.homMk r.hom (𝟙 _) (by
      change r.hom ≫ f.hom = (r.hom ≫ f.hom) ≫ 𝟙 _
      rw [Category.comp_id])
    retract := ?_ }
  apply Arrow.hom_ext
  · exact hr'
  · exact Category.id_comp _

/-- 概要：自由 J の右持ち上げ類は底の次数別全射。
方針：実自由随伴の持ち上げ対応。
規約：同じ自由モノイド像を使う。
使われ方：自由 J-cell を上の左持ち上げ類へ入れる。 -/
lemma generatingTrivialCofibrations_rlp :
    (_root_.SerrePositivity.DGAlgebra.generatingTrivialCofibrations (R := R)).rlp =
      (_root_.SerrePositivity.ProjectiveModel.projectiveFibrations R).inverseImage (Mon.forget (Complex R)) := by
  rw [_root_.SerrePositivity.DGAlgebra.generatingTrivialCofibrations, _root_.SerrePositivity.ModelGeneration.strictMap_rlp _root_.SerrePositivity.DGAlgebra.freeForgetAdjunction,
    _root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations_rlp]

include d in
/-- 概要：自由 J の生成左類は底で擬同型。
方針：右類の同定と AW path の持ち上げ論法を合わせる。
規約：任意の始域を許す。
使われ方：相対 cell の acyclicity。 -/
lemma generatingTrivialCofibrations_llp_le :
    (_root_.SerrePositivity.DGAlgebra.generatingTrivialCofibrations (R := R)).rlp.llp ≤
      (quasiIso (ModuleCat R) (.up ℤ)).inverseImage (Mon.forget (Complex R)) := by
  rw [_root_.SerrePositivity.DGAlgebra.generatingTrivialCofibrations_rlp]
  intro X Y f hf
  exact _root_.SerrePositivity.DGAlgebra.fibrations_llp_quasiIso d f hf

include d in
/-- 概要：元の自由 J の全相対 cell 射は底で擬同型。
方針：左持ち上げ類の余積・押し出し・超限合成の閉性を使う。
規約：cell の始域の cofibrancy を要求しない。
使われ方：右転送の acyclicity の実入力。 -/
lemma freeCells_acyclic :
    MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u} (_root_.SerrePositivity.DGAlgebra.generatingTrivialCofibrations (R := R))).pushouts ≤
      (quasiIso (ModuleCat R) (.up ℤ)).inverseImage (Mon.forget (Complex R)) := by
  apply le_trans ?_ (_root_.SerrePositivity.DGAlgebra.generatingTrivialCofibrations_llp_le d)
  rw [MorphismProperty.transfiniteCompositions_le_iff, MorphismProperty.pushouts_le_iff,
    MorphismProperty.coproducts_le_iff]
  exact MorphismProperty.le_llp_rlp _

end SerrePositivity.DGAlgebra
