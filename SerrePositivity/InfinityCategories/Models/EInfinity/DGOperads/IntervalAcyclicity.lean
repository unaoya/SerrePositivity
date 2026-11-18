module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IntervalPathObject

/-!
模型。文献の定義との比較は後で
# 余代数区間による転送の acyclicity

概要：Berger–Moerdijk 命題 4.1 の path object 論法で fibrations.llp の擬同型性を示す。
方針：終対象への持ち上げで retraction、二端点評価への持ち上げで逆合成の path を得る。
規約：任意の代数を扱い、モデル構造の存在と入力の cofibrancy を仮定しない。
使われ方：自由像の J-cell 射の acyclicity と完全な右転送を導く。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- 概要：fibrations.llp の代数射には retraction と逆合成の path がある（BM 命題 4.1）。
方針：零代数への射と good path object の評価への持ち上げを順に取る。
規約：fibration は底の全次数全射で判定する。
使われ方：底の射が擬同型であることを示す。 -/
lemma exists_retraction_path (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit)
    {X Y : P.Algebra} (f : X ⟶ Y)
    (hf : ((_root_.SerrePositivity.ProjectiveModel.projectiveFibrations A).inverseImage (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P)).llp f) :
    ∃ r : Y ⟶ X, f ≫ r = 𝟙 X ∧
      ∃ h : Y ⟶ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraPathFunctor hP I).obj Y,
        h ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraEvaluationNat hP I false).app Y = r ≫ f ∧
        h ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.algebraEvaluationNat hP I true).app Y = 𝟙 Y := by
  let qX := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.toTerminal P X
  let qY := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.toTerminal P Y
  let s : CommSq (𝟙 X) f qX qY := ⟨by
    apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.terminalAlgebraIsTerminal P).hom_ext⟩
  obtain ⟨r⟩ := ((hf qX (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.toTerminal_projectiveFibration P X)).sq_hasLift s).exists_lift
  have hr : f ≫ r.l = 𝟙 X := r.fac_left
  let Q := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.prepathAlgebra hP I Y
  let pair : Y ⟶ Y ⨯ Y := prod.lift (r.l ≫ f) (𝟙 Y)
  let t : CommSq (f ≫ Q.ι) f Q.p pair := ⟨by
    apply prod.hom_ext
    · simp only [Category.assoc, PrepathObject.p_fst, Q.ι_p₀,
        Category.comp_id, pair, prod.lift_fst]
      rw [← Category.assoc, hr, Category.id_comp]
    · simp only [Category.assoc, PrepathObject.p_snd, Q.ι_p₁,
        Category.comp_id, pair, prod.lift_snd]⟩
  obtain ⟨h⟩ := ((hf Q.p (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.prepathAlgebra_p_projectiveFibration hP I Y)).sq_hasLift t).exists_lift
  refine ⟨r.l, hr, h.l, ?_, ?_⟩
  · have hh := congrArg (fun a => a ≫ prod.fst) h.fac_right
    simpa only [Category.assoc, PrepathObject.p_fst, pair,
      prod.lift_fst, Q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.prepathAlgebra] using hh
  · have hh := congrArg (fun a => a ≫ prod.snd) h.fac_right
    simpa only [Category.assoc, PrepathObject.p_snd, pair,
      prod.lift_snd, Q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.prepathAlgebra] using hh

/-- 概要：fibrations に左持ち上げ性を持つ代数射は底で擬同型（BM 命題 4.1）。
方針：path の終端からその本体の擬同型性を得て、始端の逆合成から retract を取る。
規約：転送モデル構造の存在と代数の cofibrancy を仮定しない。
使われ方：右転送に必要な J-cell acyclicity を導く。 -/
lemma fibrations_llp_quasiIso (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval hP.counit)
    {X Y : P.Algebra} (f : X ⟶ Y)
    (hf : ((_root_.SerrePositivity.ProjectiveModel.projectiveFibrations A).inverseImage (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P)).llp f) :
    QuasiIso f.hom := by
  obtain ⟨r, hr, h, h₀, h₁⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.exists_retraction_path hP I f hf
  have hr' : f.hom ≫ r.hom = 𝟙 X.carrier := congrArg _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.hom hr
  have h₀' : h.hom ≫ I.evaluation Y.carrier false = r.hom ≫ f.hom :=
    congrArg _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.hom h₀
  have h₁' : h.hom ≫ I.evaluation Y.carrier true = 𝟙 Y.carrier :=
    congrArg _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.hom h₁
  have := I.evaluation_quasiIso Y.carrier true
  have : QuasiIso (h.hom ≫ I.evaluation Y.carrier true) := by
    rw [h₁']; infer_instance
  have : QuasiIso h.hom := quasiIso_of_comp_right h.hom (I.evaluation Y.carrier true)
  have := I.evaluation_quasiIso Y.carrier false
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

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval
