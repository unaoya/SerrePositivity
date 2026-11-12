module
public import SerrePositivity.KST.SConstruction.DiagonalIterationNaturality

/-! # 反復自己関手の自然な座標比較の core 実現
概要：最内側の S と対角反復の自然同型を core の実現へ移す。
方針：入力での評価、core への忘却、対角実現で自然同型を写す。
規約：既存の内側の実現との比較は別に照合する。使われ方：反復経路の標的の座標比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
attribute [local instance] CategoryTheory.endofunctorMonoidalCategory

/-- 概要：安定な入力の自己関手を固定入力で評価して core を取る関手。
方針：評価、底の単体集合への忘却、既存の core 関手を合成する。
規約：core の定義は α2 のもの。使われ方：座標比較の実現への移送。 -/
def stableEndofunctorCoreEvaluation (X : StableModel.{u}) :
    (StableModel.{u} ⥤ StableModel.{u}) ⥤ SSet.{u} :=
  (evaluation StableModel.{u} StableModel.{u}).obj X ⋙ stableModelForget ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor

/-- 概要：最内側に S を置いた反復の単体的 core 図式。
方針：自然な合成の自己関手の図式を入力で評価して core に送る。
規約：単体作用素は自己関手の水平合成で与える。使われ方：全対角の座標比較の源。 -/
def diagonalInnerSCoreDiagram (r : ℕ) (X : StableModel.{u}) : SimplicialObject SSet.{u} :=
  (simplicialStableEndofunctor ⊗ diagonalSEndofunctor r) ⋙ stableEndofunctorCoreEvaluation X

/-- 概要：最内側 S の core 図式から元の対角反復の core 図式への自然同型。
方針：単体的自己関手の座標比較を入力評価と core で写す。
規約：全ての単体作用素について自然。使われ方：対角実現の同型。 -/
def diagonalInnerSCoreDiagramIso (r : ℕ) (X : StableModel.{u}) :
    diagonalInnerSCoreDiagram r X ≅
      diagonalSEndofunctor (r + 1) ⋙ stableEndofunctorCoreEvaluation X :=
  Functor.isoWhiskerRight (diagonalSInnerComparisonNatIso r) (stableEndofunctorCoreEvaluation X)

/-- 概要：最内側 S の合成の core の全対角は既存の多重 core S の実現と同型。
方針：構成した単体的 core の自然同型を対角実現で写す。
規約：単体集合の実際の同型。使われ方：反復の境界図式の標的の座標比較。 -/
def diagonalInnerSRealizationIso (r : ℕ) (X : StableModel.{u}) :
    simplicialDiagonalFunctor.obj (diagonalInnerSCoreDiagram r X) ≅
      multiDiagonalCoreSConstruction (r + 1) X :=
  simplicialDiagonalFunctor.mapIso (diagonalInnerSCoreDiagramIso r X)

/-- 概要：既存の最内側 S の二重対角模型と、自己関手の水平合成による模型は同型。
方針：各次数では恒等を使い、内側の作用と外側の作用の順序を自然性で交換する。
規約：全単体作用素について可換。使われ方：既存の境界の標的から座標比較への橋渡し。 -/
def iteratedSRealizationInnerIso (r : ℕ) (X : StableModel.{u}) :
    iteratedSRealization r X ≅ simplicialDiagonalFunctor.obj (diagonalInnerSCoreDiagram r X) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro d e f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    apply ConcreteCategory.hom_ext
    intro z
    let P := stableSConstructionDiagram X
    let F := diagonalSEndofunctor r
    let H := stableModelForget ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor
    have hn := (F.map f).naturality (P.map f)
    have hh := congrArg (fun k => (H.map k).app d z) hn
    change (H.obj ((F.obj e).obj (P.obj e))).map f
        ((H.map ((F.obj d).map (P.map f) ≫ (F.map f).app (P.obj e))).app d z) =
      (H.obj ((F.obj e).obj (P.obj e))).map f
        ((H.map ((simplicialStableEndofunctor.map f ⊗ₘ
          (diagonalSEndofunctor r).map f).app X)).app d z)
    rw [endofunctorMonoidalCategory_tensorMap_app]
    exact congrArg ((H.obj ((F.obj e).obj (P.obj e))).map f) hh)

/-- 概要：最内側の S の反復実現は既存の多重 core S の実現と同型。
方針：二重対角の作用の順序の交換と、自己関手の全単体的座標比較を合成する。
規約：実際の単体集合の同型。使われ方：反復した経路境界の標的の照合。 -/
def iteratedSRealizationCoordinateIso (r : ℕ) (X : StableModel.{u}) :
    iteratedSRealization r X ≅ multiDiagonalCoreSConstruction (r + 1) X :=
  iteratedSRealizationInnerIso r X ≪≫ diagonalInnerSRealizationIso r X

end SerrePositivity.KST.SConstruction
