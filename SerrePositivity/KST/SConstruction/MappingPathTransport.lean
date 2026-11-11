module
public import SerrePositivity.KST.SConstruction.PointedMappingPathSections
public import SerrePositivity.KST.Spectra.PathNaturality

/-! # 可換正方形による mapping path の移送
概要：元の点つき射の可換正方形を mapping path の厳密な射へ移す。
方針：自由 path の後合成と源の射を引き戻しへ貼る。
規約：始点・終点・源への射影を厳密に保つ。
使われ方：一方向比較の逆射の混合切断空間。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalClosed SSet
open Spectra

/-- 自由 path の後合成は両端点の評価と厳密に可換。 -/
lemma freePathMap_endpoint {Y Z : PointedSimplicialSet.{u}} (b : Y ⟶ Z) (i : Fin 2) :
    PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} b ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Z i =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y i ≫ b := by
  unfold _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
  change (ihom _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u}).map b ≫ (MonoidalClosed.pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint.{u} i)).app Z ≫
      (MonoidalClosed.unitNatIso (C := PointedSimplicialSet.{u})).inv.app Z =
    ((MonoidalClosed.pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint.{u} i)).app Y ≫
      (MonoidalClosed.unitNatIso (C := PointedSimplicialSet.{u})).inv.app Y) ≫ b
  rw [← Category.assoc, ← MonoidalClosed.pre_comm_ihom_map, Category.assoc,
    (MonoidalClosed.unitNatIso (C := PointedSimplicialSet.{u})).inv.naturality b]
  rfl

/-- 元の射の可換正方形を mapping path の射へ移す。 -/
def mappingPathTransport {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : a ≫ f' = f ≫ b) : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath f ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath f' :=
  pullback.lift
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f ≫ PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} b)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f ≫ a) (by
      rw [Category.assoc, freePathMap_endpoint, ← Category.assoc,
        pullback.condition, Category.assoc, ← h, ← Category.assoc]
      rfl)

/-- mapping path の移送は自由 path 成分と可換。 -/
lemma mappingPathTransport_path {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : a ≫ f' = f ≫ b) :
    mappingPathTransport f f' a b h ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y' 1) f' =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f ≫ PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} b :=
  pullback.lift_fst ..

/-- mapping path の移送は元の源への射影と可換。 -/
lemma mappingPathTransport_retraction {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : a ≫ f' = f ≫ b) :
    mappingPathTransport f f' a b h ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f' =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f ≫ a := pullback.lift_snd ..

/-- mapping path の移送は終点への射影と可換。 -/
lemma mappingPathTransport_projection {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : a ≫ f' = f ≫ b) :
    mappingPathTransport f f' a b h ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f' =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f ≫ b := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection]
  rw [← Category.assoc, mappingPathTransport_path, Category.assoc,
    freePathMap_endpoint, Category.assoc]

/-- mapping path の移送は恒等正方形を恒等射へ送る。 -/
lemma mappingPathTransport_id {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    mappingPathTransport f f (𝟙 X) (𝟙 Y) (by simp) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [mappingPathTransport_path, Category.id_comp]
    have h := (PointedObject.basedHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u}).map_id Y
    exact (congrArg (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f ≫ ·) h).trans (Category.comp_id _)
  · change mappingPathTransport f f (𝟙 X) (𝟙 Y) _ ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f =
      𝟙 (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath f) ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f
    rw [mappingPathTransport_retraction, Category.comp_id, Category.id_comp]

/-- mapping path の移送は正方形の合成を厳密に保つ。 -/
lemma mappingPathTransport_comp {X Y X' Y' X'' Y'' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (f'' : X'' ⟶ Y'')
    (a : X ⟶ X') (b : Y ⟶ Y') (a' : X' ⟶ X'') (b' : Y' ⟶ Y'')
    (h : a ≫ f' = f ≫ b) (h' : a' ≫ f'' = f' ≫ b')
    (hh : (a ≫ a') ≫ f'' = f ≫ (b ≫ b')) :
    mappingPathTransport f f' a b h ≫ mappingPathTransport f' f'' a' b' h' =
      mappingPathTransport f f'' (a ≫ a') (b ≫ b') hh := by
  apply pullback.hom_ext
  · rw [Category.assoc, mappingPathTransport_path, ← Category.assoc,
      mappingPathTransport_path, Category.assoc, mappingPathTransport_path]
    exact congrArg (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f ≫ ·)
      ((PointedObject.basedHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u}).map_comp b b').symm
  · change (mappingPathTransport f f' a b h ≫ mappingPathTransport f' f'' a' b' h') ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f'' =
      mappingPathTransport f f'' (a ≫ a') (b ≫ b') hh ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f''
    rw [Category.assoc, mappingPathTransport_retraction, ← Category.assoc,
      mappingPathTransport_retraction, mappingPathTransport_retraction, Category.assoc]

end SerrePositivity.KST.SConstruction
