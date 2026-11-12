module

public import SerrePositivity.KST.Spectra.UnbasedRestrictionFiberNaturality
public import SerrePositivity.KST.Spectra.PointedCofiberComparison
public import SerrePositivity.KST.Spectra.PointedFibrationNaturality

/-!
概要：源の可換正方形に沿う制限 fiber の比較と連結準同型の自然性。
方針：反変な写像空間の正方形を fiber へ送り、相対商の正方形と照合する。
規約：連結準同型には源の単射性と係数の Kan 性だけを要求する。
使われ方：Goerss–Jardine VIII §1。骨格の微分を各セルの境界へ制限する。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace UnbasedPointedMapping

variable {A B C D : SSet.{u}} (i : A ⟶ B) (j : C ⟶ D)
  (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ i = j ≫ b)

include h

lemma pre_square (Y : PointedSimplicialSet.{u}) :
    pre i Y ≫ pre a Y = pre b Y ≫ pre j Y := by
  apply Under.UnderMorphism.ext
  change ((MonoidalClosed.pre i).app Y.right) ≫ ((MonoidalClosed.pre a).app Y.right) =
    ((MonoidalClosed.pre b).app Y.right) ≫ ((MonoidalClosed.pre j).app Y.right)
  rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, h,
    MonoidalClosed.pre_map, NatTrans.comp_app]

/-- 概要：源の可換正方形が誘導する相対商の射。
方針：自由基点を加えた正方形を通常の cofiber の比較へ送る。
規約：写像空間とは逆向きに相対商を写す。
使われ方：Goerss–Jardine VIII §1。セル球面から骨格の相対商への包含。 -/
def relativeSourceMap : relativeSource j ⟶ relativeSource i :=
  PointedCofiberComparison.map (PointedObject.adjoinFunctor.map j)
    (PointedObject.adjoinFunctor.map i) (PointedObject.adjoinFunctor.map a)
    (PointedObject.adjoinFunctor.map b) (by
      simp only [← Functor.map_comp, h])

@[reassoc]
lemma relativeSourceMap_projection :
    pointedCofiberProjection (PointedObject.adjoinFunctor.map j) ≫
        relativeSourceMap i j a b h =
      PointedObject.adjoinFunctor.map b ≫
        pointedCofiberProjection (PointedObject.adjoinFunctor.map i) :=
  PointedCofiberComparison.projection_map _ _ _ _ _

/-- 概要：源の正方形に沿う実際の制限 fiber の射。
方針：通常の前合成の正方形へ pointed fiber の関手性を適用する。
規約：Kan 性はこの構成には不要。
使われ方：Goerss–Jardine VIII §1。塔の fiber をセルごとの fiber へ制限する。 -/
def restrictionSourceFiberMap (Y : PointedSimplicialSet.{u}) :
    pointedFiber (pre i Y) ⟶ pointedFiber (pre j Y) :=
  PointedFiberComparison.map (pre i Y) (pre j Y) (pre b Y) (pre a Y)
    (pre_square i j a b h Y)

@[reassoc]
lemma restrictionSourceFiberMap_ι (Y : PointedSimplicialSet.{u}) :
    restrictionSourceFiberMap i j a b h Y ≫ pointedFiberι (pre j Y) =
      pointedFiberι (pre i Y) ≫ pre b Y :=
  PointedFiberComparison.map_ι _ _ _ _ _

/-- 概要：相対商からの写像空間と制限 fiber の同型は源の正方形に自然。
方針：fiber 包含の後で商射と自由基点 Hom の前合成を照合する。
規約：厳密な点つき射の等式。
使われ方：Goerss–Jardine VIII §1。セル係数と連結準同型の自然性を接続する。 -/
@[reassoc]
lemma restrictionFiberIso_source (Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (relativeSourceMap i j a b h) Y ≫
        (restrictionFiberIso j Y).hom =
      (restrictionFiberIso i Y).hom ≫ restrictionSourceFiberMap i j a b h Y := by
  apply pointedFiber_hom_ext (pre j Y)
  rw [Category.assoc, restrictionFiberIso_hom_ι, Category.assoc,
    restrictionSourceFiberMap_ι, restrictionFiberIso_hom_ι_assoc]
  have hp := congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed f Y)
    (relativeSourceMap_projection i j a b h)
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp] at hp
  have hc := congrArg (fun f ↦ f ≫ (freeHomIso D Y).hom) hp
  simp only [Category.assoc] at hc
  have hf := freeHomIso_pre b Y
  rw [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hf
  exact hc.trans (congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed
    (pointedCofiberProjection (PointedObject.adjoinFunctor.map i)) Y ≫ f) hf)

instance pre_fibration (f : A ⟶ B) [Mono f] (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] : Fibration (pre f Y).right := by
  change Fibration ((MonoidalClosed.pre f).app Y.right)
  infer_instance

/-- 概要：源の単射の正方形で制限 fiber の連結準同型は可換。
方針：実際の点つき fibration の自然性を前合成の正方形へ適用する。
規約：モデル圏のインスタンスを仮定しない。
使われ方：Goerss–Jardine I §8、VIII §1。骨格の微分のセルへの制限。 -/
theorem restrictionSourceFiberMap_connecting [Mono i] [Mono j]
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (r : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (obj A Y).right (r + 1) (obj A Y).basepoint) :
    pointedGroupMap r (restrictionSourceFiberMap i j a b h Y)
        (pointedConnectingHom (pre i Y) r x) =
      pointedConnectingHom (pre j Y) r (pointedGroupMap (r + 1) (pre a Y) x) :=
  pointedConnectingHom_natural (pre i Y) (pre j Y) (pre b Y) (pre a Y)
    (pre_square i j a b h Y) r x

end UnbasedPointedMapping
end
end SerrePositivity.KST.Spectra
