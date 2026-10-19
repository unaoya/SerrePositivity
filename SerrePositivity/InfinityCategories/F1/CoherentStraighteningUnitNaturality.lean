module

public import SerrePositivity.InfinityCategories.F1.CoherentStraighteningUnitCounit
public import SerrePositivity.InfinityCategories.F1.CoherentStraighteningCounitNaturality
public import SerrePositivity.InfinityCategories.F1.UniversalCoherentReconstructionCounitComponents
public import SerrePositivity.InfinityCategories.F1.FunctorIsoPrecompositionCoherence

/-!
概要：指定した単位変換の底変換と普遍単位の成分の整合性。
方針：余単位の自然性と実際の単位の辺の逆同型との一致を使う。
規約：対象ごとの新たな単位を選ばない。
使われ方：単位・余単位を同じ比較にそろえた自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：指定した単位の同型は分類の制限比較と通常の前合成に関して可換。
方針：余単位の底変換の可換式を逆にして同じ制限比較を合成する。
規約：実際の単位の辺に由来する同型を使う。
使われ方：任意の底変換に対する単位側の自然性。 -/
lemma coherentStraighteningUnit_baseChange_naturality {B D : SSet.{u + 1}}
    (F : D ⟶ SpaceInfinity.{u}) (G : B ⟶ SpaceInfinity.{u})
    (g : D ⟶ B) (h : g ≫ G = F) :
    coherentStraighteningUnitIso F ≪≫ coherentStraighteningRestrictionDiagramIso F G g h =
      (eqToIso (congrArg (fun d ↦ SSet.HomotopyCategory.mk (functorVertex d)) h)).symm ≪≫
        (coherentStraighteningUnitIso G).precomp g := by
  have hn := coherentStraighteningCounit_baseChange_naturality F G g h
  have he := congrArg (fun e ↦ e.symm ≪≫ coherentStraighteningRestrictionDiagramIso F G g h) hn
  simpa [coherentStraighteningUnitIso_eq_counit_symm, FunctorIso.precomp_symm,
    Iso.trans_symm, Iso.trans_assoc] using he.symm

/-- 概要：普遍単位の実際の成分を分類の成分比較へ続けると指定した単位となる。
方針：普遍余単位の成分の一致を反転し同じ成分比較を合成する。
規約：普遍側でも個別側でも元の比較を使う。
使われ方：指定した単位変換と全図式の普遍比較の接続。 -/
lemma universalCoherentReconstructionUnitIso_app {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) :
    FunctorIso.app (universalCoherentReconstructionCounitIso B).symm (functorVertex F) ≪≫
      universalCoherentReconstructionComponentIso F = coherentStraighteningUnitIso F := by
  have hn := universalCoherentReconstructionCounitIso_app F
  have he := congrArg (fun e ↦ e.symm ≪≫ universalCoherentReconstructionComponentIso F) hn
  rw [FunctorIso.app_symm, coherentStraighteningUnitIso_eq_counit_symm]
  simpa [Iso.trans_symm, Iso.trans_assoc] using he

end SerrePositivity.InfinityCategories
