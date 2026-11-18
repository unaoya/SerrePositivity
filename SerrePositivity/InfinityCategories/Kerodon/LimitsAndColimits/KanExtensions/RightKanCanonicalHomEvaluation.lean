module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanCanonicalRestriction
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality

/-!
概要：元の標準右Kan錐で前合成した全二胞体の頂点成分を、元の指定頂点で評価する。
方針：既存の二胞体の前合成の評価則と、同じ標準形状の頂点等式を使う。
規約：HTT §4.3.2、Kerodon §7.3（Tag 02Y1）の既存構成の計算法則。
使われ方：S8 の指定大域比較の同じ成分を、標準錐の頂点で照合する。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

private lemma evaluate_vertex_eq {C D : SSet.{u}} {U V : C ⟶ D}
    (α : FunctorHom U V) {x y : C _⦋0⦌} (h : x = y) :
    functorHomEvaluate α x ≫
      eqToHom (congrArg (fun z => (HomotopyCategory.mk (V.app _ z) : hoFunctor.obj D)) h) =
    eqToHom (congrArg (fun z => (HomotopyCategory.mk (U.app _ z) : hoFunctor.obj D)) h) ≫
      functorHomEvaluate α y := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 元の全二胞体を標準形状で前合成しても、指定頂点での成分は同じ。 -/
lemma rightKanCanonicalShape_hom_apex {K C D : SSet.{u}} (δ : K ⟶ C)
    (c : C _⦋0⦌) {U V : C ⟶ D} (α : FunctorHom U V) :
    let a := (joinInl (Δ[0] : SSet.{u}) (rightKanShape δ c)).app _
      (stdSimplex.obj₀Equiv.symm 0)
    functorHomEvaluate (U := rightKanCanonicalShape δ c ≫ U)
      (V := rightKanCanonicalShape δ c ≫ V)
      ((hoFunctor.map ((pre (rightKanCanonicalShape δ c)).app D)).toFunctor.map α) a ≫
      eqToHom (congrArg (fun z => (HomotopyCategory.mk (V.app _ z) : hoFunctor.obj D))
        (rightKanCanonicalShape_apex δ c)) =
    eqToHom (congrArg (fun z => (HomotopyCategory.mk (U.app _ z) : hoFunctor.obj D))
      (rightKanCanonicalShape_apex δ c)) ≫ functorHomEvaluate α c := by
  dsimp only
  rw [functorHomEvaluate_precomp α (rightKanCanonicalShape δ c)]
  exact evaluate_vertex_eq α (rightKanCanonicalShape_apex δ c)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
