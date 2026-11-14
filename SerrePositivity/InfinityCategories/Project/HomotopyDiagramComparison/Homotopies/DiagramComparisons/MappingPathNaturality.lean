module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FreeInterval
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMappingNaturality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.RelativePointedHomLifting
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.TowerMatchingLifting
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.FreePathSpace
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.MappingPathSpace
public import SerrePositivity.Spectra.Pointed.Basic
public import SerrePositivity.Spectra.Pointed.InternalHom
public import SerrePositivity.Spectra.Pointed.SmashMonoidal
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
概要：点つき射の可換正方形に対する mapping path の自然性。
方針：内部 Hom の自然性から端点と定数 path の式を得て、引き戻しの普遍性へ渡す。
規約：自由区間の端点一が源側、端点零が標的側。
使われ方：Goerss–Jardine I §7、BF 1978 §2、Sp の塔の比較の因子分解。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：自由 path の後合成は端点評価と可換。
方針：源の制限の自然性と単位からの内部 Hom の標準同型の自然性を使う。
規約：両端点と任意の点つき射に対する厳密な等式。
使われ方：mapping path に誘導される射と二つの射影の自然性。 -/
lemma freePathEndpoint_naturality {Y Z : PointedSimplicialSet.{u}} (f : Y ⟶ Z) (k : Fin 2) :
    PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} f ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Z k =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y k ≫ f := by
  simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, Category.assoc]
  change (ihom _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u}).map f ≫
      (MonoidalClosed.pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint.{u} k)).app Z ≫
        (unitNatIso (C := PointedSimplicialSet.{u})).inv.app Z = _
  rw [← Category.assoc, (MonoidalClosed.pre (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint.{u} k)).naturality f,
    Category.assoc, (unitNatIso (C := PointedSimplicialSet.{u})).inv.naturality f,
    ← Category.assoc]
  rfl

/-- 概要：定数 path は任意の点つき後合成と可換。
方針：区間の潰す射による制限と単位の標準同型の自然性を使う。
規約：ホモトピーではなく点つき射の等式。
使われ方：mapping path の塔への定数 path の比較射。 -/
lemma freeConstantPath_naturality {Y Z : PointedSimplicialSet.{u}} (f : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeConstantPath Y ≫ PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} f =
      f ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeConstantPath Z := by
  simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeConstantPath, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre, Category.assoc]
  change (unitNatIso (C := PointedSimplicialSet.{u})).hom.app Y ≫
      (MonoidalClosed.pre _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalCollapse.{u}).app Y ≫ (ihom _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u}).map f = _
  rw [← (MonoidalClosed.pre _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalCollapse.{u}).naturality f, ← Category.assoc,
    ← (unitNatIso (C := PointedSimplicialSet.{u})).hom.naturality f, Category.assoc]
  rfl

/-- 概要：可換正方形が mapping path の間に誘導する点つき射。
方針：path の後合成と源の射を二つの成分として引き戻しへ持ち上げる。
規約：元の射は f、f'、縦の射は a、b。
使われ方：段ごとの mapping path を逆向きの塔へまとめる。 -/
def mappingPathMap {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ f') : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath f ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath f' :=
  pullback.lift
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f ≫ PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} b)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f ≫ a) (by
      rw [Category.assoc, freePathEndpoint_naturality, ← Category.assoc, pullback.condition,
        Category.assoc, h, ← Category.assoc]
      rfl)

/-- 概要：mapping path の比較射は path 成分の後合成と可換。
方針：引き戻しへの持ち上げの第一成分を計算する。
規約：自由 path への射影をそのまま保持する。
使われ方：端点評価と相対比較の検証。 -/
lemma mappingPathMap_path {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ f') :
    mappingPathMap f f' a b h ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y' 1) f' =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f ≫ PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} b :=
  pullback.lift_fst ..

/-- 概要：mapping path の比較射は元の源への射影と可換。
方針：引き戻しへの持ち上げの第二成分を計算する。
規約：点つき射として厳密に可換。
使われ方：mapping path の塔から元の源の塔への射。 -/
lemma mappingPathMap_source {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ f') :
    mappingPathMap f f' a b h ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f' = _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f ≫ a :=
  pullback.lift_snd ..

/-- 概要：mapping path の比較射は元の標的への終点射と可換。
方針：path 成分と端点評価の自然性を合成する。
規約：元の標的の射 b と厳密に可換。
使われ方：mapping path の塔から元の標的の塔への射。 -/
lemma mappingPathMap_target {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ f') :
    mappingPathMap f f' a b h ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f' = _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f ≫ b := by
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection, ← Category.assoc, mappingPathMap_path, Category.assoc,
    freePathEndpoint_naturality, ← Category.assoc]
  rfl

/-- 概要：定数 path の比較射は mapping path の可換正方形に関して自然。
方針：引き戻しの両射影の後で定数 path と源の自然性を検査する。
規約：各段の厳密な因子分解を保つ。
使われ方：元の源の塔から mapping path の塔への射。 -/
lemma mappingPathMap_unit {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ f') :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit f ≫ mappingPathMap f f' a b h = a ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit f' := by
  apply pullback.hom_ext
  · rw [Category.assoc, mappingPathMap_path]
    simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit, pullback.lift_fst_assoc, Category.assoc, pullback.lift_fst]
    rw [freeConstantPath_naturality, ← Category.assoc, h, Category.assoc]
  · change (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit f ≫ mappingPathMap f f' a b h) ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f' = _
    rw [Category.assoc, mappingPathMap_source, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit_retraction,
      Category.id_comp]
    simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathUnit, Category.assoc, pullback.lift_snd, Category.comp_id]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
