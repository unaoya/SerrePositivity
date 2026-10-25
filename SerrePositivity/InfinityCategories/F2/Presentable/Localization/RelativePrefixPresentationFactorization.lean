module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.RelativeCompactCoconeFactorization
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.TerminalPrefixFilteredPresentation

/-!
概要：元の filtered 表示に沿い、全前置図式を厳密に固定する compact 余錐の一段因子化を作る。
方針：元の前置図式の coslice 上の共終表示を構成し、相対一段因子化へ渡す。
規約：表示変更は固定図式の等号だけとし、全余錐と元の表示脚を保持する。
使われ方：HTT 5.5.4.13 の交互構成の各再帰段に適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits

private lemma cosliceEqIso_vertex_val {J C : SSet.{u + 1}} {p q : J ⟶ C}
    (h : p = q) (z : JoinCocone p) :
    (((eqToIso (congrArg sliceUnder h)).hom.app _ z) : JoinCocone q).val = z.val := by
  cases h
  rfl

/-- 小さい全前置図式を保持する因子化を、元の同じ filtered 表示の後続段に作る。 -/
lemma compactDiagram_factorization_over_terminalPrefixPresentation
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {J K I : SSet.{u}} [Quasicategory J] [Quasicategory K] [Quasicategory I]
    [IsKappaFiltered μ I] (hJ : IsKappaSmall μ J) (hK : IsKappaSmall μ K)
    (t : K _⦋0⦌) (ht : IsTerminalVertex t) (a : K ⟶ I)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : HasSmallColimits C)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ C) (c : JoinCocone D) (hc : IsColimitCone c)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶ C)
    (hQ : ∀ j, Compact.IsKappaCompact.{u, u + 1} μ (q.app _ j))
    (i : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj J)
    [Mono i] (hp : i ≫ q = (SSet.uliftFunctor.{u + 1, u}).map a ≫ D)
    (z : JoinCocone q)
    (hz : (z.restrict i).val = (c.restrict ((SSet.uliftFunctor.{u + 1, u}).map a)).val) :
    let b := (SSet.uliftFunctor.{u + 1, u}).map a
    let s := (uliftSliceUnderIso.{u, u + 1} a).hom
    let e := eqToIso (congrArg sliceUnder hp.symm)
    let F := s ≫ sliceUnderPostcomp b D ≫ e.hom
    let v := mapJoinCocone e.hom (sourceCosliceRestrictedCocone b s D c)
    ∃ j : (sliceUnder a) _⦋0⦌, ∃ w : JoinCocone q,
      w.restrict i = F.app _ (ULift.up j) ∧
      ∃ k : (sliceUnder q).Edge w z,
        (k.map (sliceUnderRestrict q i)).edge =
          (Compact.coconeTransportLeg v (ULift.up j)).edge := by
  let b := (SSet.uliftFunctor.{u + 1, u}).map a
  let s := (uliftSliceUnderIso.{u, u + 1} a).hom
  let e := eqToIso (congrArg sliceUnder hp.symm)
  let v₀ := sourceCosliceRestrictedCocone b s D c
  let F := s ≫ sliceUnderPostcomp b D ≫ e.hom
  let v := mapJoinCocone e.hom v₀
  have hμreg : μ.IsRegular := Fact.out
  have : IsKappaFiltered μ (sliceUnder a) := isKappaFiltered_sliceUnder hμreg hK a
  have hv₀ : IsColimitCone v₀ :=
    terminalPrefix_restrictedCocone_isColimit hK t ht a D c hc
  have hv : IsColimitCone v :=
    (equivalence_isColimitCone_iff (qCatEquivalenceOfIso e).isQCatEquivalence v₀).mp hv₀
  have hzv : z.restrict i = v.vertex := by
    apply Subtype.ext
    have hvraw : v.vertex.val = (c.restrict b).val := by
      change (e.hom.app _ v₀.vertex).val = (c.restrict b).val
      rw [cosliceEqIso_vertex_val hp.symm v₀.vertex, sourceCosliceRestrictedCocone_vertex]
    exact hz.trans hvraw.symm
  exact compactDiagram_factorization_relative_terminalPrefix hμ hJ hC q hQ i (ULift.up t)
    ((isTerminalVertex_iff_ulift.{u, u + 1} t).mp ht) F v hv z hzv

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
