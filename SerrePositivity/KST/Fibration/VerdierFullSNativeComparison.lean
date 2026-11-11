module
public import SerrePositivity.KST.Fibration.VerdierFullSNativeLongHom

/-!
概要：元の上下二胞体と核円柱の全 S• 比較を、同じ native Kan 座標で保持する。
方針：元の実比較辺を標的座標同型へ写し、同じ固定部分のまま内部評価する。
規約：共有対角・元の実合成端・全比較パラメータを保持する。
使われ方：指定 Verdier 四角形の全図式比較の二つの三角柱入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 同じ実比較辺の native 座標像は、元の共有対角上で厳密に恒等。 -/
def verdierNullHomFullSNativeComparison (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :
    FixedRestrictionFunctorEdge coherentTriangleDirectVertexMap
      (verdierNullHomFullSNativeFamily d j) (verdierNullHomFullSNativeFamily d k) := by
  have h := (verdierNullHomFullSComparison d j k).postcomp
    ((ihom (fullSRealizationKanObject ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)).obj).map
      (coreSingleKanIso ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)).hom)
  simpa only [verdierNullHomFullSNativeFamily, zeroFunctorFullSNativeKanFamily,
    Category.assoc] using h

/-- 元の全上下円柱の同じ比較辺は、native 座標でも共有対角の全評価を固定する。 -/
def verdierNullHomFullSNativeCylinderComparison (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j k : Fin 2) :=
  (verdierNullHomFullSNativeComparison d j k).uncurryCoreKan

/-- 元の核収縮族を、同じ全 S• 始域と native Kan 標的の全族へ送る。 -/
def verdierNullContractionFullSNativeFamily (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    (Δ[1] : SSet.{u}) ⟶
      (ihom (fullSRealizationKanObject ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)).obj).obj
        ((stableMultiKanEnrichedFunctor 0).obj ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)).obj :=
  zeroStableHomFamilyLift (verdierNullContractionFamily d)
    (zeroEndPostcompFamily_zero_vertices _ _) ≫
      zeroFunctorFullSNativeKanFamily ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
        ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)

/-- 元の指定下側二胞体の path 族を、同じ全 S• の native 族に延長する。 -/
def verdierNullPathFullSNativeFamily (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) (j : Fin 2) :
    (Δ[1] : SSet.{u}) ⟶
      (ihom (fullSRealizationKanObject ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)).obj).obj
        ((stableMultiKanEnrichedFunctor 0).obj ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)).obj :=
  zeroStableHomFamilyLift (verdierNullPathFamily d j) (verdierNullPathFamily_zero d j) ≫
    zeroFunctorFullSNativeKanFamily ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)
      ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)

/-- 元の核収縮と指定下側二胞体の同じ比較辺を、実合成端固定のまま native 座標へ送る。 -/
def verdierNullContractionFullSNativeComparison (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    FixedRestrictionFunctorEdge (stdSimplex.δ (0 : Fin 2))
      (verdierNullContractionFullSNativeFamily d) (verdierNullPathFullSNativeFamily d 1) := by
  have h := (verdierNullContractionFullSComparison d).postcomp
    ((ihom (fullSRealizationKanObject ((verdierNullDiagonal d).obj ⟨ULift.up 0⟩)).obj).map
      (coreSingleKanIso ((verdierNullDiagonal d).obj ⟨ULift.up 1⟩)).hom)
  simpa only [verdierNullContractionFullSNativeFamily, verdierNullPathFullSNativeFamily,
    zeroFunctorFullSNativeKanFamily, Category.assoc] using h

/-- 同じ全 native 円柱比較の内部評価も、元の実合成端を厳密に固定する。 -/
def verdierNullContractionFullSNativeCylinderComparison (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :=
  (verdierNullContractionFullSNativeComparison d).uncurryCoreKan

/-- 元の同じ実可逆辺から得る、全 native 円柱の全関手同型。 -/
def verdierNullContractionFullSNativeCylinderIso (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :=
  (verdierNullContractionFullSNativeCylinderComparison d).iso

end SerrePositivity.KST.Fibration
