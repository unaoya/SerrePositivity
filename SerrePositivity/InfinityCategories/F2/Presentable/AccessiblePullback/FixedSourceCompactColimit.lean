module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.FixedSourceOrdinalColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.OrdinalCompactColimits

/-!
概要：固定入力の下で、長さ κ₀ の成分図式の compact な最終余極限を構成する。
方針：底の κ₀-filtered 余極限を同じ固定始域の下へ戻し、小順序余極限の compact 閉性を使う。
規約：全小余極限や入力図式の余極限を要求しない。
使われ方：元の成分と底への像が共に μ-compact な入力付き成分対。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：入力付き成分列には元の成分とその像が共に μ-compact な最終余極限がある。
方針：同じ固定始域内の余錐の射影を使って二つの compact 閉性を判定する。
規約：κ₀-filtered 余極限の存在と保存だけを要求する。
使われ方：相対交互構成での入力付き compact 成分対の最終段。 -/
lemma exists_fixedSourceOrdinalColimit_compact_image
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ)
    {K C B : SSet.{u + 1}} [Quasicategory K] [Quasicategory C] [Quasicategory B]
    (hC : Ind.HasSmallKappaFilteredColimits κ C)
    (p : C ⟶ B) (hpc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ p) (a : K ⟶ C)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve κ.ord.ToType) ⟶ sliceUnder a)
    (hD : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ
      ((D ≫ sliceUnderProjection a).app (Opposite.op ⦋0⦌) v))
    (hDp : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ
      ((D ≫ sliceUnderProjection a ≫ p).app (Opposite.op ⦋0⦌) v)) :
    ∃ d : JoinCocone D, IsColimitCone d ∧
      Compact.IsKappaCompact.{u, u + 1} μ
        ((sliceUnderProjection a).app (Opposite.op ⦋0⦌) d.vertex) ∧
      Compact.IsKappaCompact.{u, u + 1} μ
        ((sliceUnderProjection a ≫ p).app (Opposite.op ⦋0⦌) d.vertex) := by
  have := Cardinal.nonempty_ord_toType (c := κ) (Cardinal.IsRegular.ne_zero Fact.out)
  letI := WellFoundedLT.toOrderBot κ.ord.ToType
  have := ordinalNerve_isKappaFiltered κ
  obtain ⟨d, hd⟩ := fixedSource_orderBot_hasColimit a κ.ord.ToType D
    (hC (nerve κ.ord.ToType) (D ≫ sliceUnderProjection a))
  have hd₀ : IsColimitCone (mapJoinCocone (sliceUnderProjection a) d) :=
    (fixedSource_orderBot_isColimitCone_iff_projection a κ.ord.ToType D d).mp hd
  have hsmall : HasCardinalLT κ.ord.ToType μ := by
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_toType, Cardinal.card_ord] using h.1
  have hc := isMuCompact_smallPosetColimit_universe.{u, u + 1}
    h κ.ord.ToType hsmall (mapJoinCocone (sliceUnderProjection a) d) hd₀ hD
  rw [Ind.mapJoinCocone_vertex] at hc
  let d₀ := mapJoinCocone (sliceUnderProjection a) d
  have hd₁ := hpc (nerve κ.ord.ToType) (D ≫ sliceUnderProjection a) d₀ hd₀
  have hc' := isMuCompact_smallPosetColimit_universe.{u, u + 1}
    h κ.ord.ToType hsmall (mapJoinCocone p d₀) hd₁ hDp
  rw [Ind.mapJoinCocone_vertex, Ind.mapJoinCocone_vertex] at hc'
  exact ⟨d, hd, hc, hc'⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
