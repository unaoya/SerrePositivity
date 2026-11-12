module

public import SerrePositivity.KST.Spectra.LoopMappingPositiveEquiv
public import SerrePositivity.KST.Spectra.FreeMappingPointedIso

/-!
概要：定数基点の通常の写像空間と loop の順序を交換する。
方針：自由基点を加えた源からの Hom の同型を通して、点つき Hom の交換同型を移す。
規約：源の基点も Kan 性も要求しない。
使われ方：Goerss–Jardine VIII §1。骨格の塔を loop に送る比較。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 通常の写像空間の loop と、loop 値の写像空間の点つき同型。 -/
def loopSwap (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (obj K Y) ≅ obj K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) :=
  ((ihom PointedSimplicialSet.circle.{u}).mapIso (freeHomIso K Y)).symm ≪≫
    PointedMapping.loopSwap (PointedObject.adjoin K) Y ≪≫ freeHomIso K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)

/-- 自由基点からの Hom の同型は loop との交換と整合する。 -/
@[reassoc]
lemma loopSwap_freeHom (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) :
    PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (freeHomIso K Y).hom ≫
      (loopSwap K Y).hom =
    (PointedMapping.loopSwap (PointedObject.adjoin K) Y).hom ≫
      (freeHomIso K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).hom := by
  change (ihom PointedSimplicialSet.circle.{u}).map (freeHomIso K Y).hom ≫
    ((ihom PointedSimplicialSet.circle.{u}).map (freeHomIso K Y).inv ≫ _) = _
  rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- 概要：通常の写像空間の loop 交換は源への制限に自然。
方針：自由基点の同型を前合成してから、二つの既存の源自然性を合成する。
規約：源の射は任意。
使われ方：Goerss–Jardine VIII §1。骨格遷移の可換正方形。 -/
@[reassoc]
lemma loopSwap_pre {K L : SSet.{u}} (f : K ⟶ L) (Y : PointedSimplicialSet.{u}) :
    PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (pre f Y) ≫
      (loopSwap K Y).hom = (loopSwap L Y).hom ≫ pre f (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) := by
  apply (cancel_epi
    ((ihom PointedSimplicialSet.circle.{u}).mapIso (freeHomIso L Y)).hom).mp
  have hf :
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.adjoinFunctor.map f) Y) ≫
        PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (freeHomIso K Y).hom =
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (freeHomIso L Y).hom ≫
        PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (pre f Y) := by
    have h := freeHomIso_pre f Y
    rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
    have hh := congrArg ((PointedObject.basedHomFunctor
      PointedSimplicialSet.circle.{u}).map) h
    simp only [Functor.map_comp] at hh
    exact hh
  change PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (freeHomIso L Y).hom ≫
    (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (pre f Y) ≫ _) = _
  rw [← Category.assoc, ← hf, Category.assoc, loopSwap_freeHom]
  rw [← Category.assoc]
  have hs := PointedMapping.loopSwap_pre
    (A := PointedObject.adjoin K) (B := PointedObject.adjoin L)
    (PointedObject.adjoinFunctor.map f) Y
  rw [hs]
  rw [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, freeHomIso_pre]
  have hlast := congrArg (fun g ↦ g ≫ pre f (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)) (loopSwap_freeHom L Y).symm
  simp only [Category.assoc] at hlast
  exact hlast

end
end SerrePositivity.KST.Spectra.UnbasedPointedMapping
