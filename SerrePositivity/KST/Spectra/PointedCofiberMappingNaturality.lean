module

public import SerrePositivity.KST.Spectra.PointedCofiberMappingFiberIso
public import SerrePositivity.KST.Spectra.PointedFiberComparison

/-!
概要：cofiber の Hom と制限の fiber の比較の係数自然性。
方針：fiber の包含で比較し、cofiber の射影への前合成の自然性を使う。
規約：Kan 性は不要。点つき射の厳密な等式。
使われ方：Goerss–Jardine VIII §1。骨格のセルの係数表示の自然性。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PointedMapping

@[reassoc]
lemma prePointed_post {A B Y Z : PointedSimplicialSet.{u}} (i : A ⟶ B) (p : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y ≫ PointedObject.basedHomMap A (Y := Y) (Z := Z) p =
      PointedObject.basedHomMap B (Y := Y) (Z := Z) p ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z := by
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  exact ((MonoidalClosed.pre i).naturality p).symm

end PointedMapping

/-- 概要：cofiber の Hom の fiber 比較の後の包含は商射による制限。
方針：fiber の底の基点の移送を含め、基礎比較の包含の式を使う。
規約：実際の点つき射の等式。
使われ方：Goerss–Jardine VIII §1。係数自然性を包含で確認する式。 -/
@[reassoc]
lemma pointedCofiberMappingFiberIso_hom_ι {A B : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (Y : PointedSimplicialSet.{u}) :
    (pointedCofiberMappingFiberIso i Y).hom ≫ pointedFiberι (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y) =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection i) Y := by
  apply Under.UnderMorphism.ext
  change ((cofiberMappingFiberIso i Y).hom ≫
      (fiberIsoOfEq (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y).right
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y)).symm).hom) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y).right
        ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y).right.app _
          (PointedSimplicialSet.basepoint (PointedObject.basedHom B Y))) = _
  rw [Category.assoc, fiberIsoOfEq_hom_ι]
  exact cofiberMappingFiberIso_hom_ι i Y

/-- 概要：係数射が誘導する制限射の点つき fiber の射。
方針：前合成と後合成の可換正方形を fiber へ送る。
規約：源 i に単射性を要求しない。
使われ方：Goerss–Jardine VIII §1。相対写像空間の係数射。 -/
def pointedRestrictionFiberMap {A B Y Z : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (p : Y ⟶ Z) :
    pointedFiber (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y) ⟶
      pointedFiber (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z) :=
  PointedFiberComparison.map _ _
    (PointedObject.basedHomMap B (Y := Y) (Z := Z) p)
    (PointedObject.basedHomMap A (Y := Y) (Z := Z) p) (PointedMapping.prePointed_post i p)

/-- 概要：cofiber の Hom の点つき fiber 表示は係数射に自然。
方針：fiber 包含後の商射の制限を前後合成の自然性で比較する。
規約：基礎の pullback の選択に依存する式を包含で識別する。
使われ方：Goerss–Jardine VIII §1。セルの Hom と実際の fiber の自然な同定。 -/
@[reassoc]
lemma pointedCofiberMappingFiberIso_natural {A B Y Z : PointedSimplicialSet.{u}}
    (i : A ⟶ B) (p : Y ⟶ Z) :
    PointedObject.basedHomMap (pointedCofiber i) (Y := Y) (Z := Z) p ≫
        (pointedCofiberMappingFiberIso i Z).hom =
      (pointedCofiberMappingFiberIso i Y).hom ≫ pointedRestrictionFiberMap i p := by
  apply pointedFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z)
  rw [Category.assoc, pointedCofiberMappingFiberIso_hom_ι]
  dsimp only [pointedRestrictionFiberMap]
  rw [Category.assoc, PointedFiberComparison.map_ι, ← Category.assoc,
    pointedCofiberMappingFiberIso_hom_ι]
  exact (PointedMapping.prePointed_post (pointedCofiberProjection i) p).symm

end

end SerrePositivity.KST.Spectra
