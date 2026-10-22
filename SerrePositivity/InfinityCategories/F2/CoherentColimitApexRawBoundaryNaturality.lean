module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitApexRawTriangleBoundary
public import SerrePositivity.InfinityCategories.F2.FunctorIsoPrecompNormalizedReindex

/-!
概要：元の三辺・指定 path の境界比較の候補は、任意の全初期値の再制限でも値を保つ。
方針：実端点補正を保つ前合成と、同じ二段の前合成の合成則を使う。
規約：元の全二単体と四指定因子を保持。使われ方：全族の普遍残余の照合。
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

/-- 元の境界比較候補は、任意の実係数射での二段の初期値制限と値まで整合する。 -/
lemma coherentColimitApexRawTriangleBoundaryAt_precomp {K L : SSet.{u + 1}}
    (f : K ⟶ vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone F).vertex)
    (r : L ⟶ K) :
    HEq ((coherentColimitApexRawTriangleBoundaryAt B T f).precomp r)
      (coherentColimitApexRawTriangleBoundaryAt B T (r ≫ f)) := by
  have hs : f ≫ ((coherentColimitRawFiberTransport B a ≫
      coherentColimitRawFiberTransport B b) ≫
        pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)) =
      ((f ≫ coherentColimitRawFiberTransport B a) ≫ coherentColimitRawFiberTransport B b) ≫
        pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T) := by
    simp only [Category.assoc]
  have ht := (Category.assoc f (coherentColimitRawFiberTransport B d)
    (pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T))).symm
  have hs' : (r ≫ f) ≫ ((coherentColimitRawFiberTransport B a ≫
      coherentColimitRawFiberTransport B b) ≫
        pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T)) =
      (((r ≫ f) ≫ coherentColimitRawFiberTransport B a) ≫ coherentColimitRawFiberTransport B b) ≫
        pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T) := by
    simp only [Category.assoc]
  exact functorIsoOfEq_precomp_reindex_heq
    (coherentColimitApexRawTriangleBoundaryIso B T) f r hs ht hs'
    (Category.assoc (r ≫ f) (coherentColimitRawFiberTransport B d)
      (pointedFiberValueTo (coherentColimitApex_raw_two_vertex B T))).symm

end SerrePositivity.InfinityCategories.F2
