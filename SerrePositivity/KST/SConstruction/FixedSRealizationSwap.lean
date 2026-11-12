module
public import SerrePositivity.KST.SConstruction.DiagonalSInterchange
public import SerrePositivity.KST.SConstruction.DiagonalIterationRealization
public import SerrePositivity.KST.SConstruction.MultiSOneComparison

/-! # 固定した S 方向の内外交換の core 実現
概要：固定次数の S_m の内側と外側で反復した core 図式を厳密な同型で比較する。
方針：単体的自己関手の自然な交換を入力評価・core・対角へ移す。
規約：既存の多重実現と一次方向の実現の座標を変更しない。
使われ方：経路零行の内側 S₁ を元の構造射の外側 S₁ に合わせる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial
attribute [local instance] CategoryTheory.endofunctorMonoidalCategory

/-- 固定した S_m を最内側に置いた反復 core の単体的図式。 -/
def fixedSInnerCoreDiagram (m r : ℕ) (X : StableModel.{u}) : SimplicialObject SSet.{u} :=
  (((Functor.const SimplexCategoryᵒᵖ).obj (sEndofunctor m)) ⊗ diagonalSEndofunctor r) ⋙
    stableEndofunctorCoreEvaluation X

/-- 固定した S_m を最外側に置いた反復 core の単体的図式。 -/
def fixedSOuterCoreDiagram (m r : ℕ) (X : StableModel.{u}) : SimplicialObject SSet.{u} :=
  (diagonalSEndofunctor r ⊗ ((Functor.const SimplexCategoryᵒᵖ).obj (sEndofunctor m))) ⋙
    stableEndofunctorCoreEvaluation X

/-- 固定次数の S_m の内側と外側の core 図式の全単体的な交換同型。 -/
def fixedSCoreDiagramSwapIso (m r : ℕ) (X : StableModel.{u}) :
    fixedSInnerCoreDiagram m r X ≅ fixedSOuterCoreDiagram m r X :=
  Functor.isoWhiskerRight (diagonalFixedSInterchangeNatIso m r) (stableEndofunctorCoreEvaluation X)

/-- 内側の固定 S_m の core 図式は既存の入力 S_m X の反復 core 図式に一致する。 -/
def fixedSInnerCoreDiagramIso (m r : ℕ) (X : StableModel.{u}) :
    fixedSInnerCoreDiagram m r X ≅
      multiIndexDiagonal r ⋙ multiCoreSConstruction r (sStableModel m X) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro d e f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    let H := stableModelForget.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor
    change H.map (((𝟙 (sEndofunctor m) ⊗ₘ (diagonalSEndofunctor r).map f)).app X) =
      H.map (((diagonalSEndofunctor r).map f).app (sStableModel m X))
    congr 1
    simp only [endofunctorMonoidalCategory_tensorMap_app, NatTrans.id_app,
      CategoryTheory.Functor.map_id, Category.comp_id]
    rfl)

/-- 内側の固定 S_m の対角 core 実現は元の反復実現に厳密に同型。 -/
def fixedSInnerRealizationIso (m r : ℕ) (X : StableModel.{u}) :
    (multiRealizationFunctor r).obj (sStableModel m X) ≅
      simplicialDiagonalFunctor.obj (fixedSInnerCoreDiagram m r X) :=
  (simplicialDiagonalFunctor.mapIso (fixedSInnerCoreDiagramIso m r X)).symm

/-- 外側の固定 S₁ の core 図式は元の一次方向の core 図式に厳密に同型。 -/
def fixedSOneOuterCoreDiagramIso (r : ℕ) (X : StableModel.{u}) :
    fixedSOuterCoreDiagram 1 r X ≅
      multiIndexDiagonal r ⋙ oneDirectionIndex r ⋙ multiCoreSConstruction (r + 1) X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro d e f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    let H := stableModelForget.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor
    change H.map ((((diagonalSEndofunctor r).map f ⊗ₘ 𝟙 (sEndofunctor 1))).app X) =
      H.map ((sEndofunctor 1).map (((diagonalSEndofunctor r).map f).app X) ≫
        (simplicialStableEndofunctor.map (𝟙 (Opposite.op ⦋1⦌))).app
          (((diagonalSEndofunctor r).obj e).obj X))
    rw [endofunctorMonoidalCategory_tensorMap_app, CategoryTheory.Functor.map_id]
    simp only [NatTrans.id_app]
    exact congrArg H.map ((Category.id_comp _).trans (Category.comp_id _).symm))

/-- 元の経路零行の内側 S₁ と元の構造射の外側 S₁ の実現の厳密な交換同型。 -/
def sOneInnerOuterRealizationIso (r : ℕ) (X : StableModel.{u}) :
    (multiRealizationFunctor r).obj (sStableModel 1 X) ≅
      (oneDirectionRealizationFunctor r).obj X :=
  fixedSInnerRealizationIso 1 r X ≪≫
    simplicialDiagonalFunctor.mapIso (fixedSCoreDiagramSwapIso 1 r X) ≪≫
    simplicialDiagonalFunctor.mapIso (fixedSOneOuterCoreDiagramIso r X)

end SerrePositivity.KST.SConstruction
