module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.CompactInputComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.InputFunctorColimits

/-!
概要：異なる固定入力を持つ二つの表示から共通入力上の compact 比較を構成する。
方針：元の同じ表示添字内で相対交互塔を作り、各固定入力内で最終余極限を取る。
規約：指定入力を忘れる比較は全射として与え、生成性は仮定しない。
使われ方：compact comma の成分射影の cofinal 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：異なる追加入力を保った compact 成分の像を共通入力上で比較できる。
方針：共通入力内の相対交互塔の成分を元の各入力付き表示へ戻して余極限を取る。
規約：追加入力を消さず、比較だけを共通入力まで忘れる。
使われ方：指定成分始点の下でも compact 成分対を生成する。 -/
lemma exists_relativeInputComparison_of_presentations
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ)
    {A K : SSet.{u}} [Quasicategory A] [Quasicategory K] (hK : IsKappaSmall μ K)
    (C L : Fin 2 → SSet.{u + 1}) [∀ c, Quasicategory (C c)] [∀ c, Quasicategory (L c)]
    (hCκ : ∀ c, Ind.HasSmallKappaFilteredColimits κ (C c))
    (hBκ : Ind.HasSmallKappaFilteredColimits κ (Ind.IndInfinity μ A))
    (p : ∀ c, C c ⟶ Ind.IndInfinity μ A)
    (hpκ : ∀ c, IsKappaAccessibleFunctor κ (p c))
    (hpCompact : ∀ c, ∀ v, Compact.IsKappaCompact.{u, u + 1} μ v →
      Compact.IsKappaCompact.{u, u + 1} μ ((p c).app (Opposite.op ⦋0⦌) v))
    (q : ∀ c, L c ⟶ C c) (z : ∀ c, JoinCocone (q c))
    (N : ∀ c, CompactInputPresentation μ (q c) (z c))
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ Ind.IndInfinity μ A)
    (hr : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ (r.app (Opposite.op ⦋0⦌) v))
    (t : JoinCocone r)
    (T : ∀ c, sliceOver ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (z c)) ⟶
      sliceOver ((SSet.yonedaEquiv (X := sliceUnder r)).symm t))
    (hT : ∀ c, T c ≫ sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder r)).symm t) ≫
        sliceUnderProjection r =
      sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (z c)) ≫
        sliceUnderProjection (q c) ≫ p c)
    (hcol : ∀ c, IsColimitCone (mapJoinCocone (sliceUnderProjection r)
      (sliceDiagramCocone ((N c).diagram ≫ T c)))) :
    ∃ v : ∀ c, (sliceOver ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (z c))) _⦋0⦌,
      (∀ c, Compact.IsKappaCompact.{u, u + 1} μ
        ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (z c)) ≫
          sliceUnderProjection (q c)).app (Opposite.op ⦋0⦌) (v c))) ∧
      (∀ c, Compact.IsKappaCompact.{u, u + 1} μ
        ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (z c)) ≫
          sliceUnderProjection (q c) ≫ p c).app (Opposite.op ⦋0⦌) (v c))) ∧
      Nonempty (VertexIso ((T 0).app (Opposite.op ⦋0⦌) (v 0))
        ((T 1).app (Opposite.op ⦋0⦌) (v 1))) := by
  have := Cardinal.nonempty_ord_toType (c := κ) (Cardinal.IsRegular.ne_zero Fact.out)
  letI := WellFoundedLT.toOrderBot κ.ord.ToType
  have := ordinalNerve_isKappaFiltered κ
  let P := fun c ↦ (N c).diagram ≫ T c
  have hP : ∀ c, ∀ v : (N c).index _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((P c ≫ sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder r)).symm t) ≫
        sliceUnderProjection r).app (Opposite.op ⦋0⦌) (ULift.up v)) := by
    intro c v
    have heq : P c ≫ sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder r)).symm t) ≫
        sliceUnderProjection r = (N c).diagram ≫
      sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (z c)) ≫
        sliceUnderProjection (q c) ≫ p c := by
      dsimp only [P]
      rw [Category.assoc, hT c]
    rw [heq]
    exact hpCompact c _ ((N c).compact v)
  obtain ⟨F, J, hJ⟩ := exists_relativeAlternatingDiagram_coslice_ind
    (I := fun c ↦ (N c).index) (P := P) h hK r hr hP hcol
  have hchoose (c : Fin 2) := exists_compactInputOrdinalColimit h (hCκ c) (p c) (hpκ c)
    (hpCompact c) (N c) (J c)
  choose d hd hb hc hpc using hchoose
  let b : ∀ c, JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (alternatingSection κ c)) ≫ F) := fun c ↦
    ⟨(d c).val ≫ T c, by
      rw [← Category.assoc, (d c).property]
      exact (hJ c).symm⟩
  have hbc (c : Fin 2) : IsColimitCone (b c) := by
    have hb' := inputFunctor_orderBot_isColimitCone_of_base_projection
      (q c) (p c) (hpκ c) r (z c) t (T c) (hT c) κ.ord.ToType
      ((SSet.uliftFunctor.{u + 1, u}).map (J c) ≫ (N c).diagram) (d c) (hb c)
    exact (isColimitCone_iff_of_cocone_val_eq (b c) (mapJoinCocone (T c) (d c)) rfl).mpr hb'
  have hvertex (c : Fin 2) : (b c).vertex = (T c).app (Opposite.op ⦋0⦌) (d c).vertex :=
    Ind.mapJoinCocone_vertex (T c) (d c)
  have he := alternatingFixedSourceOverColimit_vertexIso κ hBκ r F (b 0) (hbc 0) (b 1) (hbc 1)
  rw [hvertex 0, hvertex 1] at he
  exact ⟨fun c ↦ (d c).vertex, hc, hpc, he⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
