module

public import SerrePositivity.InfinityCategories.F1B.KanComplex.HomotopyClasses

/-!
概要：Kan 複体間の射の、全てのパラメータからのホモトピー類による同値判定。
方針：終域からの射の全射性で右逆を取り、始域からの射の単射性で左逆を得る。
規約：パラメータ K は任意の単体集合。射の両端の Kan 性を使う。
使われ方：Kerodon Proposition 3.1.7.17 の写像空間の判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：全パラメータからの射のホモトピー類が全単射ならホモトピー逆が存在する。
方針：K=B の全射性と K=A の単射性から同じ逆射を構成する。
規約：各点の π₀ の全単射だけではなく、全 K の写像空間で検査する。
使われ方：Kerodon Remark 3.1.7.6、Proposition 3.1.7.17。 -/
lemma isSimplicialHomotopyEquivalence_of_postcomposition_piZero_bijective
    {A B : SSet.{u}} [KanComplex A] [KanComplex B] (f : A ⟶ B)
    (h : ∀ K : SSet.{u}, Function.Bijective (SSet.mapπ₀ ((ihom K).map f))) :
    IsSimplicialHomotopyEquivalence f := by
  obtain ⟨a, ha⟩ := (h B).surjective (SSet.π₀.mk (functorVertex (𝟙 B)))
  obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨g, rfl⟩ := (functorVertexEquiv B A).surjective v
  have hgf : SSet.π₀.mk (functorVertex (g ≫ f)) = SSet.π₀.mk (functorVertex (𝟙 B)) := ha
  have hfg : SSet.π₀.mk (functorVertex (f ≫ g)) = SSet.π₀.mk (functorVertex (𝟙 A)) := by
    apply (h A).injective
    change SSet.π₀.mk (functorVertex ((f ≫ g) ≫ f)) =
      SSet.π₀.mk (functorVertex ((𝟙 A) ≫ f))
    have he := congrArg (SSet.mapπ₀ ((pre f).app B)) hgf
    change SSet.π₀.mk (functorVertex (f ≫ (g ≫ f))) =
      SSet.π₀.mk (functorVertex (f ≫ 𝟙 B)) at he
    simpa only [Category.assoc, Category.comp_id, Category.id_comp] using he
  exact ⟨g, (functorVertex_piZero_eq_iff_homotopy _ _).mp hfg,
    (functorVertex_piZero_eq_iff_homotopy _ _).mp hgf⟩

end SerrePositivity.InfinityCategories
