module

public import SerrePositivity.KST.Spectra.FreeMappingPointedIso
public import SerrePositivity.KST.Spectra.PointedCofiberMappingFiberIso
public import SerrePositivity.KST.Spectra.PointedFiberComparison

/-!
概要：定数基点の写像空間の制限の fiber を相対 cofiber からの Hom で表示する。
方針：自由基点の Hom の自然同型で制限の正方形を移し、fiber の比較同型を使う。
規約：源の射の単射性を同型の構成には仮定しない。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の塔の fiber の群の計算の模型。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：通常の源の射を定数基点の写像空間の fiber の源となる cofiber にする。
方針：源と標的に自由基点を加えてから点つき cofiber を取る。
規約：元の射の像全体と追加基点を同じ基点へ潰す。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の相対商の点つき模型。 -/
def relativeSource {K L : SSet.{u}} (f : K ⟶ L) : PointedSimplicialSet.{u} :=
  pointedCofiber (PointedObject.adjoinFunctor.map f)

/-- 概要：源の制限の点つき fiber と相対 cofiber からの Hom の同型。
方針：cofiber の Hom の fiber 表示を自由基点の Hom の自然性で移す。
規約：係数 X の Kan 性は同型の構成そのものには不要。
使われ方：Goerss–Jardine I §7、VIII §1。骨格の塔の各 fiber の点つき表示。 -/
def restrictionFiberIso {K L : SSet.{u}} (f : K ⟶ L) (X : PointedSimplicialSet.{u}) :
    PointedObject.basedHom (relativeSource f) X ≅ pointedFiber (pre f X) :=
  pointedCofiberMappingFiberIso (PointedObject.adjoinFunctor.map f) X ≪≫
    PointedFiberComparison.iso
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.adjoinFunctor.map f) X) (pre f X)
      (freeHomIso L X) (freeHomIso K X) (by
        rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
        exact freeHomIso_pre f X)

end

end SerrePositivity.KST.Spectra.UnbasedPointedMapping
