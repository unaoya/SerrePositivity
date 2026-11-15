module

public import SerrePositivity.EInfinity.Modules.CotensorUnit
public import SerrePositivity.EInfinity.Modules.CotensorCounit

/-!
# 元の加群から同じ全単体 cotensor への比較

概要：M10 の単位則と余単位則を貼り合わせ、元の加群を始域とする比較を得る。
方針：単位 cotensor の自然同型の逆と、同じ AW 余単位比較を合成する。
規約：HA §1.3.4、Reedy fibrancy は別に示す。
使われ方：同じ具体的な simplicial frame の coaugmentation。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory Opposite MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：元の加群の定数図式から同じ単体族への比較は全加群射に自然。
方針：同じ単位自然同型の逆と余単位の自然変換を合成する。
規約：HA §1.3.4、全標的と全単体。使われ方：frame の始域の固定。 -/
def moduleCotensorCoaugmentationFamily :
    Functor.const SimplexCategoryᵒᵖ ⟶ moduleCotensorSimplicesFunctor A D :=
  (Functor.leftUnitor (Functor.const SimplexCategoryᵒᵖ)).inv ≫
    CategoryTheory.Functor.whiskerRight (moduleCotensorUnitIso A D).inv
      (Functor.const SimplexCategoryᵒᵖ) ≫
      moduleCotensorCounitFamily A D

/-- 概要：同じ比較の次数成分は同じ単位同型の逆と AW 余単位前合成。
方針：自然変換の合成を評価する。
規約：HA §1.3.4、元の射の式。使われ方：弱同値の照合。 -/
lemma moduleCotensorCoaugmentationFamily_app (M : ModuleCategory A D)
    (n : SimplexCategoryᵒᵖ) :
    ((moduleCotensorCoaugmentationFamily A D).app M).app n =
      (moduleCotensorUnitIsoObj A D M).inv ≫ (moduleCotensorCounitNat A D M).app n := by
  change 𝟙 M ≫ _ ≫ _ = _
  rw [Category.id_comp]
  rfl

/-- 概要：元の加群からの同じ比較は全ての単体次数で擬同型。
方針：同じ単位同型の逆と、実収縮から得た余単位比較を合成する。
規約：HA §1.3.4、追加のモデル仮定なし。使われ方：frame の coaugmentation 条件。 -/
lemma moduleCotensorCoaugmentationFamily_weak (M : ModuleCategory A D)
    (n : SimplexCategoryᵒᵖ) :
    moduleQuasiIso A D (((moduleCotensorCoaugmentationFamily A D).app M).app n) := by
  rw [moduleCotensorCoaugmentationFamily_app]
  intro x
  rw [CategoryTheory.Functor.map_comp]
  have := moduleCotensorCounitNat_weak A D M n x
  infer_instance

end SerrePositivity.EInfinity.Modules
