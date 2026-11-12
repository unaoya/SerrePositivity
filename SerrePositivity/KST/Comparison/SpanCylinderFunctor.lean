module

public import SerrePositivity.KST.Comparison.DoubleMappingCylinderEquivalence

/-!
# span の二重写像円筒の関手

概要：実際の二重写像円筒を span の図式の関手とし、三つの頂点の包含を自然変換にまとめる。
方針：既証の比較写像の恒等・合成則と、各頂点の包含との可換性を使う。
規約：Segal 1974 Lemma 1.7 の図式の置換の整合。
使われ方：span の関手的な Kan 分解を円筒へ送り、前後の四角形を比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：WalkingSpan の図式の実際の二重写像円筒の関手。
方針：二つの脚の円筒と、成分ごとの射が誘導する比較を使う。
規約：零頂点が中央、左頂点と右頂点が両端を表す。
使われ方：関手的な span の置換の円筒への移送。
-/
def spanCylinderFunctor : (WalkingSpan ⥤ SSet.{u}) ⥤ SSet.{u} where
  obj F := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd)
  map {F G} α := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap
    (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd)
    (G.map WalkingSpan.Hom.fst) (G.map WalkingSpan.Hom.snd)
    (α.app .zero) (α.app .left) (α.app .right)
    (α.naturality WalkingSpan.Hom.fst).symm (α.naturality WalkingSpan.Hom.snd).symm
  map_id _ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap_id _ _
  map_comp {F G H} α β :=
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderMap_comp
      (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd)
      (G.map WalkingSpan.Hom.fst) (G.map WalkingSpan.Hom.snd)
      (H.map WalkingSpan.Hom.fst) (H.map WalkingSpan.Hom.snd)
      (α.app .zero) (α.app .left) (α.app .right)
      (β.app .zero) (β.app .left) (β.app .right)
      (α.naturality WalkingSpan.Hom.fst).symm (α.naturality WalkingSpan.Hom.snd).symm
      (β.naturality WalkingSpan.Hom.fst).symm (β.naturality WalkingSpan.Hom.snd).symm).symm

/--
概要：左頂点から二重写像円筒への包含は span に関して自然である。
方針：左の包含と比較写像との既証の式を使う。
規約：自然変換の定義域は左頂点の評価関手。
使われ方：左頂点のホモトピー引き戻しの置換。
-/
def spanCylinderLeft : (evaluation WalkingSpan SSet.{u}).obj .left ⟶ spanCylinderFunctor where
  app F := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd)
  naturality {_ _} α := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_left_map _ _ _ _ _ _ _
    (α.naturality WalkingSpan.Hom.fst).symm (α.naturality WalkingSpan.Hom.snd).symm).symm

/--
概要：右頂点から二重写像円筒への包含は span に関して自然である。
方針：右の包含と比較写像との既証の式を使う。
規約：自然変換の定義域は右頂点の評価関手。
使われ方：右頂点のホモトピー引き戻しの置換。
-/
def spanCylinderRight : (evaluation WalkingSpan SSet.{u}).obj .right ⟶ spanCylinderFunctor where
  app F := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right (F.map WalkingSpan.Hom.fst) (F.map WalkingSpan.Hom.snd)
  naturality {_ _} α := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_right_map _ _ _ _ _ _ _
    (α.naturality WalkingSpan.Hom.fst).symm (α.naturality WalkingSpan.Hom.snd).symm).symm

/--
概要：中央の頂点から零端点を経由する円筒への写像は span に関して自然である。
方針：左脚の自然性と、左の包含の自然性を合成する。
規約：中央の頂点は左脚を経由して円筒へ送る。
使われ方：中央の頂点のホモトピー引き戻しの置換。
-/
def spanCylinderCenter : (evaluation WalkingSpan SSet.{u}).obj .zero ⟶ spanCylinderFunctor where
  app F := F.map WalkingSpan.Hom.fst ≫ spanCylinderLeft.app F
  naturality {F G} α := by
    change α.app .zero ≫ (G.map WalkingSpan.Hom.fst ≫ spanCylinderLeft.app G) =
      (F.map WalkingSpan.Hom.fst ≫ spanCylinderLeft.app F) ≫ spanCylinderFunctor.map α
    rw [← Category.assoc, ← α.naturality WalkingSpan.Hom.fst, Category.assoc]
    rw [show α.app .left ≫ spanCylinderLeft.app G =
      spanCylinderLeft.app F ≫ spanCylinderFunctor.map α from spanCylinderLeft.naturality α]
    exact (Category.assoc _ _ _).symm

/--
概要：任意の頂点から二重写像円筒への自然な写像。
方針：中央・左・右の頂点の既定の自然変換を選ぶ。
規約：中央の頂点は零端点を経由する。
使われ方：三頂点の四角形を同じ界面で置換する。
-/
def spanCylinderVertex (d : WalkingSpan) :
    (evaluation WalkingSpan SSet.{u}).obj d ⟶ spanCylinderFunctor := by
  rcases d with (_ | _ | _)
  · exact spanCylinderCenter
  · exact spanCylinderLeft
  · exact spanCylinderRight

/--
概要：span の各成分が局所化同型である射は、円筒の局所化同型へ送られる。
方針：二重写像円筒の既証の模型の不変性を三成分に適用する。
規約：貼り合わせ定理の本体を仮定するものではない。
使われ方：Kan 分解の単位の円筒での可逆性。
-/
theorem spanCylinderFunctor_map_localized_isIso {F G : WalkingSpan ⥤ SSet.{u}} (α : F ⟶ G)
    (hα : ∀ d, IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map (α.app d))) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (spanCylinderFunctor.map α)) :=
  doubleMappingCylinderMap_localized_isIso _ _ _ _ _ _ _
    (α.naturality WalkingSpan.Hom.fst).symm (α.naturality WalkingSpan.Hom.snd).symm
    (hα .zero) (hα .left) (hα .right)

end SerrePositivity.KST.Comparison
