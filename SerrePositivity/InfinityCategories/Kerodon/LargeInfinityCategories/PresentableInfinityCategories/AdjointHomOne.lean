module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AdjointHomOneNaturality

/-!
概要：元の全関手圏に表示した随伴の Hom₁ の逆対応。
方針：QCat の二胞体の表示同値に双圏の Hom 全単射を挟む。
規約：始域・標的の関手を保持し、元の Hom の合成に対する自然性を示す。
使われ方：内部 Hom の転置による前合成随伴の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

local instance adjointHomOneCategory (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

/-- 概要：右随伴による始域前合成の Hom を左随伴による標的前合成の Hom に移す。
方針：双圏の Hom₁ の逆対応を元の h Fun に表示する。
規約：全関手圏の元の二胞体を使う。
使われ方：転置の間に挟む随伴の Hom 全単射。 -/
def adjointHomOneEquiv {C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)
    (U : C ⟶ E) (V : D ⟶ E) : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (R ≫ U) V ≃ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U (L ≫ V) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (R ≫ U) V).symm.trans
    (a.homEquiv₁.symm.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv U (L ≫ V)))

/-- 概要：表示した Hom₁ 逆対応は標的の Hom の合成に自然。
方針：双圏の自然性を表示し、左 whisker を前合成の作用に移す。
規約：元の Hom を端点の変更なしに比較する。
使われ方：前合成随伴の右自然性。 -/
lemma adjointHomOneEquiv_comp {C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)
    {U : C ⟶ E} {V V' : D ⟶ E}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (R ≫ U) V) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V V') :
    adjointHomOneEquiv a U V' (α ≫ β) =
      adjointHomOneEquiv a U V α ≫ (hoFunctor.map ((pre L).app E)).toFunctor.map β := by
  let α' := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (R ≫ U) V).symm α
  let β' := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv V V').symm β
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv U (L ≫ V')) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointHomOneSymm_comp a α' β')
  change adjointHomOneEquiv a U V' (α ≫ β) =
    adjointHomOneEquiv a U V α ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (L ≫ V) (L ≫ V') (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap L ◁ β') at h
  exact h.trans (congrArg (adjointHomOneEquiv a U V α ≫ ·)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerLeft L (F := V) (G := V') β'))

/-- 概要：表示した Hom₁ 逆対応は始域の Hom の合成に自然。
方針：単位の交換則による双圏の自然性を元の Hom に移す。
規約：右随伴による前合成の射作用を明示する。
使われ方：前合成随伴の左自然性。 -/
lemma adjointHomOneEquiv_precomp {C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)
    {U U' : C ⟶ E} {V : D ⟶ E}
    (γ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U' U) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (R ≫ U) V) :
    adjointHomOneEquiv a U' V
        ((hoFunctor.map ((pre R).app E)).toFunctor.map γ ≫ α) =
      γ ≫ adjointHomOneEquiv a U V α := by
  let γ' := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv U' U).symm γ
  let α' := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (R ≫ U) V).symm α
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv U' (L ≫ V)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointHomOneSymm_precomp a γ' α')
  change adjointHomOneEquiv a U' V
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (R ≫ U') (R ≫ U) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap R ◁ γ') ≫ α) =
    γ ≫ adjointHomOneEquiv a U V α at h
  have hw := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerLeft R (F := U') (G := U) γ'
  exact (congrArg (fun t ↦ adjointHomOneEquiv a U' V (t ≫ α)) hw.symm).trans h

/-- 概要：表示した Hom₁ 逆対応は後合成の作用に自然。
方針：双圏の結合子を保つ自然性を表示し、QCat の厳密結合性で正規化する。
規約：任意の後合成関手と元の Hom を扱う。
使われ方：前合成随伴の全パラメータ自然性。 -/
lemma adjointHomOneEquiv_postcomp {C D E E' : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E] [Quasicategory E']
    {L : C ⟶ D} {R : D ⟶ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)
    {U : C ⟶ E} {V : D ⟶ E} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (R ≫ U) V) (k : E ⟶ E') :
    adjointHomOneEquiv a (U ≫ k) (V ≫ k)
      ((hoFunctor.map ((ihom D).map k)).toFunctor.map α) =
    (hoFunctor.map ((ihom C).map k)).toFunctor.map (adjointHomOneEquiv a U V α) := by
  let α' := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (R ≫ U) V).symm α
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (U ≫ k) (L ≫ (V ≫ k)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.adjointHomOneSymm_whiskerRight a α' (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap k))
  simp only [Bicategory.Strict.associator_eqToIso, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id] at h
  change adjointHomOneEquiv a (U ≫ k) (V ≫ k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv ((R ≫ U) ≫ k) (V ≫ k) (α' ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap k)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv (U ≫ k) ((L ≫ V) ≫ k) (a.homEquiv₁.symm α' ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap k) at h
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerRight (U := R ≫ U) (V := V) α' k
  have h₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCell_whiskerRight (U := U) (V := L ≫ V) (a.homEquiv₁.symm α') k
  exact (congrArg (adjointHomOneEquiv a (U ≫ k) (V ≫ k)) h₁.symm).trans (h.trans h₂)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
