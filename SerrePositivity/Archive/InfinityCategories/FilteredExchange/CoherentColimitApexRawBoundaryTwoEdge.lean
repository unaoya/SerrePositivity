module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexRawCompositeValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoDownHorizontal

/-!
概要：任意の全初期値でも、元の四因子境界の長辺値の消去は同じ二辺因子を返す。
方針：元の消去式へ前合成し、共有する中間の結合表示を同じ等式で補正する。
規約：元の raw 三辺・指定三角形・全初期値を保持する。
使われ方：Nlong と Ncomp から元の右辺へ戻す際の値の整理。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "V₀" => pointedFiberValueTo (coherentColimitApex_raw_zero_vertex B T)
local notation "V₂" => pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)
local notation "ta" => coherentColimitRawFiberTransport B a
local notation "tb" => coherentColimitRawFiberTransport B b
local notation "td" => coherentColimitRawFiberTransport B d

/-- 概要：全初期値で境界式の長辺値を消去。方針：前合成と共有端点補正。
規約：元の全因子を保持。使われ方：値比較の最後の長辺因子を除く。 -/
lemma coherentColimitApexRawTriangleBoundaryAt_long_cancel {K : SSet.{u + 1}}
    (q : K ⟶ vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone F).vertex) :
    coherentColimitApexRawTriangleBoundaryAt B T q ≪≫
        functorIsoOfEq ((coherentColimitApexRawLongValueIso B T).precomp q)
          (Category.assoc q td V₂).symm rfl =
      coherentColimitApexRawCompositeValueAt B T q ≪≫
        (FunctorIso.precomp (coherentColimitApexTriangleLiftIso B T).symm V₀).precomp q := by
  have h := congrArg (fun e => FunctorIso.precomp e q)
    (coherentColimitApexRawTriangleBoundaryIso_long_cancel B T)
  simp only [functorIso_precomp_trans] at h
  have hs : q ≫ ((ta ≫ tb) ≫ V₂) = ((q ≫ ta) ≫ tb) ≫ V₂ := by
    simp only [Category.assoc]
  have hn := congrArg (fun e => functorIsoOfEq e hs rfl) h
  rw [functorIsoOfEq_trans (hg := (Category.assoc q td V₂).symm),
    functorIsoOfEq_trans (hg := rfl)] at hn
  exact hn

end SerrePositivity.InfinityCategories.F2
