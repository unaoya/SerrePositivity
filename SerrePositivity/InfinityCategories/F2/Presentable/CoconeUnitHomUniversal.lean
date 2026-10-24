module

public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeUnitHomMap

/-!
概要：普遍余錐の単位による頂点からの Hom 写像は全単射。
方針：右頂点評価の全単射と底制限の全単射を同じ単位で比較する。
規約：指定した native な普遍余錐を保持する。
使われ方：余極限関手と定値関手の随伴の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：円錐から定値図式への射の native な頂点評価は全単射。
方針：評価関手の全単射に端点の表示の同型を補う。
規約：元の余錐頂点と指定した標的を使う。
使われ方：普遍余錐の単位の Hom 判定。 -/
lemma coconeHomApex_bijective {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : JoinCocone p) (y : X _⦋0⦌) :
    Function.Bijective (fun α : FunctorHom c.val (SSet.const y) ↦
      functorHomEvaluate α (coconeRightApexVertex K) ≫
        eqToHom (congrArg HomotopyCategory.mk (ssetConst_zero_apply y _))) := by
  let e := Iso.homCongr
    (eqToIso (congrArg HomotopyCategory.mk
      (evaluateFunctorAt_functorVertex (coconeRightApexVertex K) c.val)))
    (eqToIso (congrArg HomotopyCategory.mk
      ((evaluateFunctorAt_functorVertex (coconeRightApexVertex K) (SSet.const y)).trans
        (ssetConst_zero_apply y _))))
  have h := e.bijective.comp (coneApex_homEvaluation_bijective c.val y)
  convert h using 1
  funext α
  simp only [e, Function.comp_apply, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    functorHomEvaluate, Category.assoc, eqToHom_trans]

/-- 概要：指定した普遍余錐の単位による Hom 写像は全単射。
方針：頂点評価に沿う単位の因子化で、底制限の普遍性を移す。
規約：元の余錐と元の単位を使う。
使われ方：全パラメータの随伴判定。 -/
lemma coconeUnitHom_bijective {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : JoinCocone p) (hc : IsColimitCone c) (y : X _⦋0⦌) :
    Function.Bijective (fun β : (HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶
      HomotopyCategory.mk y ↦ coconeUnitHom c ≫ constantFunctorHomMap K β) := by
  let a : FunctorHom c.val (SSet.const y) →
      ((HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶ HomotopyCategory.mk y) := fun α ↦
    functorHomEvaluate α (coconeRightApexVertex K) ≫
      eqToHom (congrArg HomotopyCategory.mk (ssetConst_zero_apply y _))
  have ha : Function.Bijective a := coconeHomApex_bijective c y
  let e := F1B.kanFunctorHomCongr c.property (SSet.comp_const (joinInl K Δ[0]) y)
  have hr := homMap_bijective_of_initialBoundaryLifting (coconeRestriction K X)
    (functorVertex c.val) ((isColimitCone_iff_initialBoundaryLifting c).mp hc)
    (functorVertex (SSet.const y))
  have hb := e.bijective.comp hr
  constructor
  · intro β γ h
    obtain ⟨α, hα⟩ := ha.2 β
    obtain ⟨δ, hδ⟩ := ha.2 γ
    have h' : e ((hoFunctor.map ((pre (joinInl K Δ[0])).app X)).toFunctor.map α) =
        e ((hoFunctor.map ((pre (joinInl K Δ[0])).app X)).toFunctor.map δ) := by
      rw [← coconeUnitHom_evaluation c y α, ← coconeUnitHom_evaluation c y δ]
      change coconeUnitHom c ≫ constantFunctorHomMap K (a α) =
        coconeUnitHom c ≫ constantFunctorHomMap K (a δ)
      exact (congrArg (fun β ↦ coconeUnitHom c ≫ constantFunctorHomMap K β) hα).trans
        (h.trans (congrArg (fun β ↦ coconeUnitHom c ≫ constantFunctorHomMap K β) hδ).symm)
    have heq : α = δ := hb.1 h'
    exact hα.symm.trans ((congrArg a heq).trans hδ)
  · intro η
    obtain ⟨α, hα⟩ := hb.2 η
    exact ⟨a α, (coconeUnitHom_evaluation c y α).trans hα⟩

end SerrePositivity.InfinityCategories.F2.Presentable
