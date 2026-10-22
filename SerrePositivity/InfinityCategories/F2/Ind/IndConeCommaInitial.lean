module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeCommaRestriction
public import SerrePositivity.InfinityCategories.F2.Ind.CoconeTrivialLift
public import SerrePositivity.InfinityCategories.F2.Ind.IndCommaKappaCocone
public import SerrePositivity.InfinityCategories.Core.NerveCone

/-!
概要：始対象形状の元の Ind 全錐 comma を同じ始対象での実 comma へ制限する。
方針：slice 制限の自明 Kan 性と点の Yoneda 正規化を使い、元の余錐を持ち上げる。
規約：元の始点射影と全境界を保つ。使われ方：有限半順序形状の頂点追加。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C] {K : SSet.{u + 1}}
  (D : K ⟶ IndInfinity κ C) (i : (Δ[0] : SSet.{u + 1}) ⟶ K)

/-- 点上の元の図式の slice を、同じ元の評価頂点の slice へ表示変更する。 -/
def indConeCommaPointIso :
    pullback (indYoneda κ C) (sliceOverProjection (i ≫ D)) ≅
      leftKanShape (indYoneda κ C) (SSet.yonedaEquiv (i ≫ D)) :=
  eqToIso (congrArg (fun p : (Δ[0] : SSet.{u + 1}) ⟶ IndInfinity κ C =>
    pullback (indYoneda κ C) (sliceOverProjection p))
      (Equiv.symm_apply_apply SSet.yonedaEquiv (i ≫ D)).symm)

/-- 元の全錐の comma を、同じ指定点の元の Ind comma へ制限する。 -/
def indConeCommaPointRestriction :
    pullback (indYoneda κ C) (sliceOverProjection D) ⟶
      leftKanShape (indYoneda κ C) (SSet.yonedaEquiv (i ≫ D)) :=
  coneCommaRestriction (indYoneda κ C) D i ≫ (indConeCommaPointIso κ D i).hom

/-- 元の C の始点への射影は、全点制限でも厳密に保たれる。 -/
lemma indConeCommaPointRestriction_projection :
    indConeCommaPointRestriction κ D i ≫
      leftKanProjection (indYoneda κ C) (SSet.yonedaEquiv (i ≫ D)) =
        pullback.fst (indYoneda κ C) (sliceOverProjection D) := by
  have h : (indConeCommaPointIso κ D i).hom ≫
      leftKanProjection (indYoneda κ C) (SSet.yonedaEquiv (i ≫ D)) =
        pullback.fst (indYoneda κ C) (sliceOverProjection (i ≫ D)) :=
    slicePullbackTransport_projection (indYoneda κ C)
      (Equiv.symm_apply_apply SSet.yonedaEquiv (i ≫ D)).symm
  rw [indConeCommaPointRestriction, Category.assoc, h, coneCommaRestriction_fst]

/-- 始点包含が left anodyne なら元の点制限は自明 Kan。 -/
lemma indConeCommaPointRestriction_trivialKanFibration [Mono i]
    (hi : leftAnodyneExtensions i) :
    TrivialKanFibration (indConeCommaPointRestriction κ D i) := by
  have h := coneCommaRestriction_trivialKanFibration (indYoneda κ C) D i hi
  exact ⟨trivialKanFibrations.comp_mem _ _ h.mem
    (trivialKanFibrations.of_isIso (indConeCommaPointIso κ D i).hom)⟩

/-- 元の始対象形状の全錐 comma では、κ-small な全試験図式が余錐を持つ。 -/
lemma nonempty_indConeComma_cocone [Fact κ.IsRegular] [Mono i]
    (hi : leftAnodyneExtensions i) {A : SSet.{u}} (hA : IsKappaSmall κ A)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      pullback (indYoneda κ C) (sliceOverProjection D)) : Nonempty (JoinCocone q) := by
  have := indConeCommaPointRestriction_trivialKanFibration κ D i hi
  obtain ⟨c⟩ := nonempty_indComma_cocone κ (SSet.yonedaEquiv (i ≫ D)) hA
    (q ≫ indConeCommaPointRestriction κ D i)
  obtain ⟨d, _⟩ := exists_cocone_lift_of_trivialKanFibration
    (indConeCommaPointRestriction κ D i) q c
  exact ⟨d⟩

/-- 通常の始対象を持つ形状では、元の全錐 comma 上の小さい試験図式に余錐が存在。 -/
lemma nonempty_indConeComma_cocone_of_initial [Fact κ.IsRegular]
    {I : Type (u + 1)} [Category.{u + 1} I] (D₀ : nerve I ⟶ IndInfinity κ C)
    {j : I} (hj : IsInitial j) {A : SSet.{u}} (hA : IsKappaSmall κ A)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      pullback (indYoneda κ C) (sliceOverProjection D₀)) : Nonempty (JoinCocone q) :=
  nonempty_indConeComma_cocone κ D₀ (nervePoint j) (nervePoint_leftAnodyne hj) hA q

/-- 上方形状の全錐 comma 内でも、指定 κ-small 図式下で余錐を作れる。 -/
lemma nonempty_indConeComma_coslice_cocone [Fact κ.IsRegular] [Mono i]
    (hi : leftAnodyneExtensions i) {A L : SSet.{u}}
    (hA : IsKappaSmall κ A) (hL : IsKappaSmall κ L)
    (p : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      pullback (indYoneda κ C) (sliceOverProjection D))
    (q : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ sliceUnder p) :
    Nonempty (JoinCocone q) := by
  let e := uliftJoinIso.{u, u + 1} A L
  obtain ⟨c⟩ := nonempty_indConeComma_cocone κ D i hi
    (isKappaSmall_join (Fact.out : κ.IsRegular) hA hL) (e.hom ≫ sliceUnderUncurry q)
  have he : e.inv ≫ (e.hom ≫ sliceUnderUncurry q) = sliceUnderUncurry q :=
    e.inv_hom_id_assoc _
  let d : JoinCocone (sliceUnderUncurry q) := he ▸ c.restrict e.inv
  exact ⟨diagramNestedCosliceDiagramCurry q Δ[0] d⟩

end SerrePositivity.InfinityCategories.F2.Ind
