module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.CompactInputAlternatingDiagram
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.CompactInputColimit

/-!
概要：元の両成分入力を保持する compact 成分対と同じ底上の比較同型を構成する。
方針：同じ表示内の長さ κ₀ の全相対交互図式の両成分余極限を比較する。
規約：全小余極限の存在・保存を仮定しない。
使われ方：compact 成分対の comma の全小図式の延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：元の両成分入力と標的を保つ compact 成分対は同じ底上で同型な像を持つ。
方針：実際の相対交互構成の両 cofinal 成分を同じ全余極限から比較する。
規約：入力からの射と元の標的への射を全単体で保持する。
使われ方：一般 accessible 引き戻しの compact 成分対による生成。 -/
lemma exists_compactInputColimitComparison
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ)
    {A K : SSet.{u}} [Quasicategory A] [Quasicategory K] (hK : IsKappaSmall μ K)
    (C : Fin 2 → SSet.{u + 1}) [∀ c, Quasicategory (C c)]
    (hC : ∀ c, IsKappaAccessible μ (C c))
    (hCκ : ∀ c, Ind.HasSmallKappaFilteredColimits κ (C c))
    (hBκ : Ind.HasSmallKappaFilteredColimits κ (Ind.IndInfinity μ A))
    (p : ∀ c, C c ⟶ Ind.IndInfinity μ A)
    (hp : ∀ c, IsKappaAccessibleFunctor μ (p c))
    (hpκ : ∀ c, IsKappaAccessibleFunctor κ (p c))
    (hpCompact : ∀ c, ∀ v, Compact.IsKappaCompact.{u, u + 1} μ v →
      Compact.IsKappaCompact.{u, u + 1} μ ((p c).app (Opposite.op ⦋0⦌) v))
    (q : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C c)
    (hqCompact : ∀ c, ∀ v, Compact.IsKappaCompact.{u, u + 1} μ
      ((q c).app (Opposite.op ⦋0⦌) v))
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ Ind.IndInfinity μ A)
    (hq : ∀ c, q c ≫ p c = r)
    (z : ∀ c, JoinCocone (q c)) (t : JoinCocone r)
    (hz : ∀ c, (z c).val ≫ p c = t.val) :
    ∃ v : ∀ c, (sliceOver ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (z c))) _⦋0⦌,
      (∀ c, Compact.IsKappaCompact.{u, u + 1} μ
        ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (z c)) ≫
          sliceUnderProjection (q c)).app (Opposite.op ⦋0⦌) (v c))) ∧
      (∀ c, Compact.IsKappaCompact.{u, u + 1} μ
        ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (z c)) ≫
          sliceUnderProjection (q c) ≫ p c).app (Opposite.op ⦋0⦌) (v c))) ∧
      Nonempty (VertexIso
        ((stableInputPostcomp (q 0) (p 0) r (hq 0) (z 0) t (hz 0)).app (Opposite.op ⦋0⦌) (v 0))
        ((stableInputPostcomp (q 1) (p 1) r (hq 1) (z 1) t (hz 1)).app (Opposite.op ⦋0⦌) (v 1))) := by
  have := Cardinal.nonempty_ord_toType (c := κ) (Cardinal.IsRegular.ne_zero Fact.out)
  letI := WellFoundedLT.toOrderBot κ.ord.ToType
  have := ordinalNerve_isKappaFiltered κ
  obtain ⟨N, F, J, hJ⟩ := exists_compactInputAlternatingDiagram h hK C hC p hp hpCompact
    q hqCompact r hq z t hz
  have hchoose (c : Fin 2) := exists_compactInputOrdinalColimit h (hCκ c) (p c) (hpκ c)
    (hpCompact c) (N c) (J c)
  choose d hd hb hc hpc using hchoose
  let T := fun c ↦ stableInputPostcomp (q c) (p c) r (hq c) (z c) t (hz c)
  let b : ∀ c, JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (alternatingSection κ c)) ≫ F) := fun c ↦
    ⟨(d c).val ≫ T c, by
      rw [← Category.assoc, (d c).property]
      exact (hJ c).symm⟩
  have hbc (c : Fin 2) : IsColimitCone (b c) := by
    have h := stableInputPostcomp_orderBot_isColimitCone (q c) (p c) (hpκ c)
      r (hq c) (z c) t (hz c) κ.ord.ToType
      ((SSet.uliftFunctor.{u + 1, u}).map (J c) ≫ (N c).diagram) (d c) (hb c)
    exact (isColimitCone_iff_of_cocone_val_eq (b c) (mapJoinCocone (T c) (d c)) rfl).mpr h
  have hvertex (c : Fin 2) : (b c).vertex = (T c).app (Opposite.op ⦋0⦌) (d c).vertex := by
    exact Ind.mapJoinCocone_vertex (T c) (d c)
  have he := alternatingFixedSourceOverColimit_vertexIso κ hBκ r F (b 0) (hbc 0) (b 1) (hbc 1)
  rw [hvertex 0, hvertex 1] at he
  exact ⟨fun c ↦ (d c).vertex, hc, hpc, he⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
