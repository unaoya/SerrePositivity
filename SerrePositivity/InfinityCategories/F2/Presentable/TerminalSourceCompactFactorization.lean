module

public import SerrePositivity.InfinityCategories.F2.Presentable.TerminalSourceCoslice
public import SerrePositivity.InfinityCategories.F2.Presentable.SourceCosliceRestrictedVertex
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactInitialFactorization
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactFactorizationTriangle

/-!
概要：終頂点を持つ全前置図式の下で、compact な頂点への指定した全余錐を後続表示段へ因子化する。
方針：元の表示を同じ coslice 内へ制限し、指定余錐の始対象性と compact 性を使う。
規約：指定した全図式・全余錐・元の表示脚を保持する。
使われ方：可算交互構成で、既存の高次整合を保つ有限前置図式の延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：指定した全前置余錐を、元の表示脚の上の実辺として一段へ因子化する。
方針：終頂点への制限による compact 判定と、coslice 内の全余錐の因子化を合成する。
規約：前置図式の高次の面を落とさず、元の余錐を辺の終点に保つ。
使われ方：交互列の coherent な有限段階の相対延長。 -/
lemma terminalSource_relative_cocone_factorization
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {I A : SSet.{u}} [Quasicategory I] [Quasicategory A] [IsKappaFiltered μ A]
    {K C : SSet.{u + 1}} [Quasicategory K] [Quasicategory C]
    (t : K _⦋0⦌) (ht : IsTerminalVertex t)
    (a : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj I)
    (s : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder a)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ C)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hs : IsRightCofinal (s ≫ sliceUnderProjection a))
    (ha : Compact.IsKappaCompact.{u, u + 1} μ ((a ≫ D).app _ t))
    (hv : Compact.IsKappaCompact.{u, u + 1} μ c.vertex)
    {L : SSet.{u + 1}} (r : L ⟶ sliceUnder (a ≫ D))
    (cr : JoinCocone r) (hcr : IsColimitCone cr)
    (hvertex : cr.vertex = (sourceCosliceRestrictedCocone a s D c).vertex) :
    let F := s ≫ sliceUnderPostcomp a D
    let v := sourceCosliceRestrictedCocone a s D c
    ∃ j : A _⦋0⦌,
      ∃ w : (vertexFiber (sliceUnderProjection r) (F.app _ (ULift.up j))) _⦋0⦌,
      ∃ k : (sliceUnder r).Edge w.val cr,
        (k.map (sliceUnderProjection r)).edge =
          (Compact.coconeTransportLeg v (ULift.up j)).edge := by
  let v := sourceCosliceRestrictedCocone a s D c
  have hvc : IsColimitCone v := by
    apply (terminalSourceCoslice_isColimitCone_iff_projection (Fact.out : μ.IsRegular)
      t ht (a ≫ D) _ v).mpr
    apply (isColimitCone_iff_of_cocone_val_eq _ (c.restrict (s ≫ sliceUnderProjection a))
      (sourceCosliceRestrictedCocone_projection a s D c)).mpr
    exact (Ind.isColimitCone_iff_restrict_rightCofinal (s ≫ sliceUnderProjection a) hs c).mp hc
  have hcompact : Compact.IsKappaCompact.{u, u + 1} μ v.vertex := by
    dsimp only [v]
    rw [sourceCosliceRestrictedCocone_vertex]
    apply isKappaCompact_terminalSourceCosliceVertex hμ t ht (a ≫ D) (c.restrict a) ha
    simpa only [JoinCocone.vertex_restrict] using hv
  have hcompactr : Compact.IsKappaCompact.{u, u + 1} μ cr.vertex := by
    rw [hvertex]
    exact hcompact
  let z : (vertexFiber (sliceUnderProjection r) v.vertex) _⦋0⦌ :=
    ⟨cr, by change cr.vertex = _; rw [pinchedConstant_zero]; exact hvertex⟩
  exact Localization.compactInitial_leftFibration_factorization (sliceUnderProjection r)
    cr hcr hcompactr _ v hvc z

/-- 概要：元の compact 構造射は、指定した始域からの表示の一段で分裂する。
方針：全余錐を元の始域の coslice 内へ移し、その恒等辺の compact 因子化を使う。
規約：同じ元の表示脚を合成辺とする実二単体を coslice 内で保持する。
使われ方：既存の表示段を保ちながら次の比較辺を選ぶ。 -/
lemma terminalSource_relative_presentation_section
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {I A : SSet.{u}} [Quasicategory I] [Quasicategory A] [IsKappaFiltered μ A]
    {K C : SSet.{u + 1}} [Quasicategory K] [Quasicategory C]
    (t : K _⦋0⦌) (ht : IsTerminalVertex t)
    (a : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj I)
    (s : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder a)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ C)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hs : IsRightCofinal (s ≫ sliceUnderProjection a))
    (ha : Compact.IsKappaCompact.{u, u + 1} μ ((a ≫ D).app _ t))
    (hv : Compact.IsKappaCompact.{u, u + 1} μ c.vertex) :
    let F := s ≫ sliceUnderPostcomp a D
    let v := sourceCosliceRestrictedCocone a s D c
    ∃ j : A _⦋0⦌,
      ∃ t : (sliceUnder (a ≫ D)).Edge v.vertex (F.app _ (ULift.up j)),
        Nonempty (t.CompStruct (Compact.coconeTransportLeg v (ULift.up j))
          (SSet.Edge.id v.vertex)) := by
  let v := sourceCosliceRestrictedCocone a s D c
  have hvc : IsColimitCone v := by
    apply (terminalSourceCoslice_isColimitCone_iff_projection (Fact.out : μ.IsRegular)
      t ht (a ≫ D) _ v).mpr
    apply (isColimitCone_iff_of_cocone_val_eq _ (c.restrict (s ≫ sliceUnderProjection a))
      (sourceCosliceRestrictedCocone_projection a s D c)).mpr
    exact (Ind.isColimitCone_iff_restrict_rightCofinal (s ≫ sliceUnderProjection a) hs c).mp hc
  have hcompact : Compact.IsKappaCompact.{u, u + 1} μ v.vertex := by
    dsimp only [v]
    rw [sourceCosliceRestrictedCocone_vertex]
    apply isKappaCompact_terminalSourceCosliceVertex hμ t ht (a ≫ D) (c.restrict a) ha
    simpa only [JoinCocone.vertex_restrict] using hv
  exact Localization.compactSource_factorization_triangle hcompact _ v hvc
    (SSet.Edge.id v.vertex)


end SerrePositivity.InfinityCategories.F2.Presentable
