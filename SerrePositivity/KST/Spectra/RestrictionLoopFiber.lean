module

public import SerrePositivity.KST.Spectra.UnbasedLoopSwap
public import SerrePositivity.KST.Spectra.LoopFiber
public import SerrePositivity.KST.Spectra.UnbasedRestrictionFiberNaturality

/-!
概要：制限の fiber と loop の交換を相対 cofiber の表示と照合する。
方針：写像空間の交換の可換正方形を fiber に送り、包含後に商射への制限を計算する。
規約：全て点つき射の厳密な等式。係数の Kan 性は不要。
使われ方：Goerss–Jardine VIII §1。骨格の塔とセル係数の loop 比較の接続。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 制限の fiber の loop と、loop 値の制限の fiber の同型。 -/
def restrictionLoopIso {K L : SSet.{u}} (f : K ⟶ L) (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (pointedFiber (pre f Y)) ≅ pointedFiber (pre f (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)) :=
  loopPointedFiberIso (pre f Y) ≪≫
    PointedFiberComparison.iso
      (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (pre f Y))
      (pre f (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)) (loopSwap L Y) (loopSwap K Y) (loopSwap_pre f Y)

/-- fiber の loop 交換は全空間への包含と可換。 -/
@[reassoc]
lemma restrictionLoopIso_hom_ι {K L : SSet.{u}} (f : K ⟶ L)
    (Y : PointedSimplicialSet.{u}) :
    (restrictionLoopIso f Y).hom ≫ pointedFiberι (pre f (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)) =
    PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (pointedFiberι (pre f Y)) ≫
      (loopSwap L Y).hom := by
  dsimp only [restrictionLoopIso, Iso.trans_hom, PointedFiberComparison.iso]
  rw [Category.assoc, PointedFiberComparison.map_ι, ← Category.assoc,
    loopPointedFiberIso_hom_ι]

/-- 逆向きの fiber の loop 交換も全空間への包含と可換。 -/
@[reassoc]
lemma restrictionLoopIso_inv_ι {K L : SSet.{u}} (f : K ⟶ L)
    (Y : PointedSimplicialSet.{u}) :
    (restrictionLoopIso f Y).inv ≫
        PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (pointedFiberι (pre f Y)) =
      pointedFiberι (pre f (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)) ≫ (loopSwap L Y).inv := by
  apply (cancel_epi (restrictionLoopIso f Y).hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, restrictionLoopIso_hom_ι,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 概要：相対 cofiber からの Hom による fiber 表示は loop 交換と整合する。
方針：fiber 包含後で、商射への前合成と自由基点の Hom の loop 交換を合成する。
規約：任意の源の射 f に対する厳密な可換式。
使われ方：Goerss–Jardine VIII §1。セル表示の正符号の比較。 -/
@[reassoc]
lemma restrictionLoopIso_cofiber {K L : SSet.{u}} (f : K ⟶ L)
    (Y : PointedSimplicialSet.{u}) :
    PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (restrictionFiberIso f Y).hom ≫
      (restrictionLoopIso f Y).hom =
    (PointedMapping.loopSwap (relativeSource f) Y).hom ≫
      (restrictionFiberIso f (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).hom := by
  apply pointedFiber_hom_ext (pre f (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y))
  rw [Category.assoc, restrictionLoopIso_hom_ι, ← Category.assoc]
  have h :
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (restrictionFiberIso f Y).hom ≫
        PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (pointedFiberι (pre f Y)) =
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
            (pointedCofiberProjection (PointedObject.adjoinFunctor.map f)) Y) ≫
        PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (freeHomIso L Y).hom := by
    have hh := congrArg ((PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map)
      (restrictionFiberIso_hom_ι f Y)
    simp only [Functor.map_comp] at hh
    exact hh
  rw [h, Category.assoc, loopSwap_freeHom, ← Category.assoc]
  have hs := PointedMapping.loopSwap_pre
    (A := PointedObject.adjoin L) (B := relativeSource f)
    (pointedCofiberProjection (PointedObject.adjoinFunctor.map f)) Y
  rw [hs]
  simp only [Category.assoc]
  rw [restrictionFiberIso_hom_ι]

end
end SerrePositivity.KST.Spectra.UnbasedPointedMapping
