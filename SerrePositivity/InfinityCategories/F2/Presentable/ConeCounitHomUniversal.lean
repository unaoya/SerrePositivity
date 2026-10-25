module

public import SerrePositivity.InfinityCategories.F2.Presentable.ConeCounitHomNaturality
public import SerrePositivity.InfinityCategories.F2.Presentable.LeftConeHomEvaluation
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeTerminalHom

/-!
概要：指定した極限錐の余単位による頂点への Hom 対応は全単射。
方針：左頂点評価と底制限の二つの全単射を、同じ錐の余単位で比較する。
規約：元の全錐と元の射を保持する。
使われ方：全錐族から定値図式の右随伴への比較の可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits SSet.Truncated.HomotopyCategory

/-- 概要：元の左頂点から底図式への標準形状ホモトピー。
方針：同じ錐円柱の両端を定値左頂点と右包含へ照合する。
規約：全錐の高次資料を保持する。
使われ方：native な錐の余単位の指定代表。 -/
def coneDomainHomotopy (K : SSet.{u}) :
    SSet.Homotopy (SSet.const (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K)))
      (joinInr (Δ[0] : SSet.{u}) K) where
  h := coneCylinderMap K
  h₀ := by
    rw [coneCylinderMap_zero, SSet.const_comp]
    have hp : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
      apply stdSimplex.obj₀Equiv.injective
      apply Fin.ext
      omega
    rw [hp, ← SSet.yonedaEquiv_comp, Category.id_comp]
    rfl
  h₁ := coneCylinderMap_one K
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 概要：元の全錐の定値頂点から図式への余単位。
方針：標準形状ホモトピーを指定した錐で写し、両端を元の頂点と図式へ輸送する。
規約：錐の極限性を定義に含めない。
使われ方：普遍錐の Hom 公式。 -/
def coneCounitHom {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCone p) :
    FunctorHom (SSet.const c.vertex) p :=
  F1B.kanFunctorHomCongr (SSet.const_comp _ c.val) c.property
    (homMk (functorEdgeOfSimplicialHomotopy
      (functorHomotopyPostcomp (coneDomainHomotopy K) c.val)))

/-- 概要：定値始域から全錐への射の左頂点評価は、端点を揃えると全単射。
方針：元の評価の全単射に、始域の定値値と頂点の表示の同型を補う。
規約：同じ評価関手の作用を使う。
使われ方：指定した錐の余単位による Hom 全単射。 -/
lemma leftConeHomApex_bijective {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : JoinCone p) (y : X _⦋0⦌) :
    Function.Bijective (fun α : FunctorHom (SSet.const y) c.val ↦
      eqToHom (congrArg HomotopyCategory.mk
        (ssetConst_zero_apply y (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K)))).symm ≫
      functorHomEvaluate α (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K))) := by
  let x := SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K)
  let e := Iso.homCongr
    (eqToIso (congrArg HomotopyCategory.mk
      ((evaluateFunctorAt_functorVertex x (SSet.const y)).trans (ssetConst_zero_apply y x))))
    (eqToIso (congrArg HomotopyCategory.mk (evaluateFunctorAt_functorVertex x c.val)))
  have h := e.bijective.comp (leftConeApex_homEvaluation_bijective c.val y)
  convert h using 1
  funext α
  simp only [e, Function.comp_apply, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom,
    functorHomEvaluate, eqToHom_trans_assoc]

/-- 概要：指定した極限錐の余単位による Hom 写像は全単射。
方針：頂点評価と相対終点の底制限の全単射を、元の余単位の因子化で照合する。
規約：元の錐と指定された余単位を使う。
使われ方：定値図式の右随伴と極限錐族の比較。 -/
lemma coneCounitHom_bijective {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : JoinCone p) (hc : IsLimitCone c) (y : X _⦋0⦌) :
    Function.Bijective (fun β : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶
      HomotopyCategory.mk c.vertex ↦ constantFunctorHomMap K β ≫ coneCounitHom c) := by
  let a : FunctorHom (SSet.const y) c.val →
      ((HomotopyCategory.mk y : hoFunctor.obj X) ⟶ HomotopyCategory.mk c.vertex) := fun α ↦
    eqToHom (congrArg HomotopyCategory.mk
      (ssetConst_zero_apply y (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K)))).symm ≫
      functorHomEvaluate α (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K))
  have ha : Function.Bijective a := leftConeHomApex_bijective c y
  let e := F1B.kanFunctorHomCongr (SSet.comp_const (joinInr Δ[0] K) y) c.property
  have hr := homMap_bijective_of_terminalBoundaryLifting (coneRestriction K X)
    (functorVertex c.val) (terminalBoundaryLifting_coneRestriction_of_isLimitCone c hc)
    (functorVertex (SSet.const y))
  have hb := e.bijective.comp hr
  let f := fun β : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶ HomotopyCategory.mk c.vertex ↦
    constantFunctorHomMap K β ≫ coneCounitHom c
  have hf : Function.Bijective (f ∘ a) := by
    convert hb using 1
    funext α
    exact constantEndpointCounitHom_evaluation _ (coneDomainHomotopy K) c.val c.property y α
  constructor
  · intro β γ h
    obtain ⟨α, rfl⟩ := ha.surjective β
    obtain ⟨δ, rfl⟩ := ha.surjective γ
    exact congrArg a (hf.injective h)
  · intro η
    obtain ⟨α, hα⟩ := hf.surjective η
    exact ⟨a α, hα⟩

end SerrePositivity.InfinityCategories.F2.Presentable
