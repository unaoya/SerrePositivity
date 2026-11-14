module

public import SerrePositivity.AlgebraicGeometry.AffineCoverProperGraphClosure
public import SerrePositivity.AlgebraicGeometry.ProperChartOpenRange
public import SerrePositivity.AlgebraicGeometry.OpenUnionGluedMap
public import SerrePositivity.AlgebraicGeometry.DenseChartRestriction
public import SerrePositivity.AlgebraicGeometry.ProperOpenChartGluing

/-!
概要：稠密な affine 被覆模型から、固有な周辺を持つ実際の固有全射を構成する。
方針：グラフ閉包内のチャート上の開部分を貼り、逆像の一致から固有性を得る。
規約：内部の被覆模型の存在は既約な Noether 対象から供給する。
使われ方：C06 の一般の対象を有限個の既約成分から扱う前の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 実際の稠密な affine 被覆模型から、固有な周辺を持つ固有全射を供給する。 -/
theorem exists_dense_affine_cover_proper_domination {X S : Scheme.{u}}
    (D : SchemeDenseAffineCoverModel X) [IsAffine S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] :
    ∃ (T P : Scheme.{u}) (h : T ⟶ X) (t : T ⟶ P) (q : P ⟶ S),
      IsProper h ∧ Surjective h ∧ IsOpenImmersion t ∧ IsProper q ∧ t ≫ q = h ≫ f := by
  classical
  letI : IsNoetherian D.base := D.base_noetherian
  letI : IsNoetherian D.common := D.common_noetherian
  letI : IsClosedImmersion D.toBase := D.toBase_closed
  letI : Surjective D.toBase := D.toBase_surjective
  haveI (i : Fin D.n) : IsNoetherian (D.chart i).toScheme := by
    letI : CompactSpace (D.chart i).toScheme :=
      QuasiCompact.compactSpace_of_compactSpace (D.chart i).ι
    exact ⟨⟩
  obtain ⟨P, p, e, Z, j, q, π, hp, he, hefac, hj, hd, hq, hπ, hjq, hbase, hproj⟩ :=
    exists_affine_cover_proper_graph_closure D f
  letI : IsOpenImmersion j := hj
  letI : IsSchemeTheoreticallyDominant j := hd
  letI : IsProper q := hq
  letI (i : Fin D.n) : IsProper (p i) := hp i
  letI (i : Fin D.n) : IsProper (π i) := hπ i
  letI (i : Fin D.n) : IsImmersion (e i) := he i
  have hcharts (i : Fin D.n) :=
    exists_proper_chart_open_range j (π i) (e i) (D.toChart i) (hproj i)
  choose V b r w hb hr hw hdw hbe hwb hwr hRange using hcharts
  letI (i : Fin D.n) : IsOpenImmersion (b i) := hb i
  letI : Nonempty (Fin D.n) := ⟨⟨0, D.n_pos⟩⟩
  have hf (i : Fin D.n) : (r i ≫ (D.chart i).ι) ≫ (D.toBase ≫ f) = b i ≫ q := by
    calc
      (r i ≫ (D.chart i).ι) ≫ (D.toBase ≫ f) =
          r i ≫ ((D.chart i).ι ≫ D.toBase ≫ f) := by simp only [Category.assoc]
      _ = r i ≫ (e i ≫ p i) := by rw [hefac i]
      _ = (r i ≫ e i) ≫ p i := by rw [Category.assoc]
      _ = (b i ≫ π i) ≫ p i := by rw [hbe i]
      _ = b i ≫ q := by rw [Category.assoc, hbase i]
  have hcommon (i : Fin D.n) : w i ≫ (r i ≫ (D.chart i).ι) = D.commonι := by
    rw [← Category.assoc, hwr i, D.toChart_fac i]
  obtain ⟨T, t, c, ww, a, ht, hc, hww, hdww, hct, hwwt, hwi, hca, has, hwwa, hcov⟩ :=
    exists_open_union_glued_map V b (D.toBase ≫ f) q j w hwb
      (fun i ↦ r i ≫ (D.chart i).ι) hf D.commonι hcommon
  letI : IsOpenImmersion t := ht
  letI (i : Fin D.n) : IsOpenImmersion (c i) := hc i
  letI : IsSchemeTheoreticallyDominant ww := hdww
  have hRanges (i : Fin D.n) : Set.range (c i) = (a ⁻¹ᵁ D.chart i : Set T) := by
    have hpi : (t ≫ π i) ≫ p i = a ≫ (D.toBase ≫ f) := by
      rw [Category.assoc, hbase i, has]
    have hla : D.toChart i ≫ (D.chart i).ι = ww ≫ a :=
      (D.toChart_fac i).trans hwwa.symm
    have hwwpi : ww ≫ (t ≫ π i) = D.toChart i ≫ e i := by
      rw [← Category.assoc, hwwt, hproj i]
    have hcompare := restrict_eq_of_common_dense_chart a (D.chart i)
      (D.toBase ≫ f) (p i) (t ≫ π i) (e i) hpi (hefac i) ww (D.toChart i) hla hwwpi
    exact range_chart_eq_preimage_of_dense_comparison a (D.chart i) t (b i) (c i)
      (hct i) (r i) (hca i) (π i) (e i) (hRange i) hcompare
  haveI : IsProper a := isProper_of_open_chart_ranges a D.chart D.chart_cover V c r hr hca hRanges
  haveI : IsDominant (ww ≫ a) := by
    rw [hwwa]
    letI : IsSchemeTheoreticallyDominant D.commonι := D.common_dense
    infer_instance
  haveI : Surjective a := surjective_of_proper_of_dense_comp ww a
  refine ⟨T, Z, a ≫ D.toBase, t, q, inferInstance, inferInstance, ht, hq, ?_⟩
  simpa only [Category.assoc] using has.symm

/-- Noether な既約対象は、固有な周辺への開包含を持つ固有全射によって覆われる。 -/
theorem exists_irreducible_noetherian_proper_domination {X S : Scheme.{u}}
    [IsNoetherian X] [IrreducibleSpace X] [IsAffine S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] :
    ∃ (T P : Scheme.{u}) (h : T ⟶ X) (t : T ⟶ P) (q : P ⟶ S),
      IsProper h ∧ Surjective h ∧ IsOpenImmersion t ∧ IsProper q ∧ t ≫ q = h ≫ f := by
  obtain ⟨D⟩ := exists_schemeDense_affine_cover_model X
  exact exists_dense_affine_cover_proper_domination D f

end SerrePositivity.AlgebraicGeometry
