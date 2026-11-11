module
public import SerrePositivity.KST.SConstruction.FixedSRealizationSwap
public import SerrePositivity.KST.SConstruction.DiagonalSInterchangeComponents

/-! # S₁ の内外交換と元の前段比較の可換性
概要：全反復の内側の S₁ 比較と外側の元の一次方向比較を厳密に照合する。
方針：交換の成分と S₁ 評価の式を core と対角に移す。
規約：元の二比較を保つ。使われ方：経路零行と元の suspension 構造射の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel

/-- S₁ を内側から外側へ移して元の一次方向比較を取ると、入力の S₁ 比較の像に一致する。 -/
lemma sOneInnerOuterRealizationIso_comparison (r : ℕ) (X : StableModel.{u}) :
    (sOneInnerOuterRealizationIso r X).hom ≫ oneDirectionRealizationComparison r X =
      (multiRealizationFunctor r).map (stableSOneComparison X) := by
  have h : (fixedSInnerCoreDiagramIso 1 r X).inv ≫
      (fixedSCoreDiagramSwapIso 1 r X).hom ≫
      (fixedSOneOuterCoreDiagramIso r X).hom ≫ oneDirectionDiagonalComparison r X =
        Functor.whiskerLeft (multiIndexDiagonal r)
          ((multiCoreSConstructionFunctor r).map (stableSOneComparison X)) := by
    apply NatTrans.ext
    funext d
    let H := stableModelForget.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor
    change (𝟙 _ ≫ H.map (((diagonalFixedSInterchangeNatIso 1 r).hom.app d).app X)) ≫
      𝟙 _ ≫ H.map (stableSOneComparison (((diagonalSEndofunctor r).obj d).obj X)) =
        H.map (((diagonalSEndofunctor r).obj d).map (stableSOneComparison X))
    rw [Category.id_comp, Category.id_comp, ← H.map_comp]
    exact congrArg H.map (diagonalFixedSInterchangeNatIso_sOneComparison r d X)
  change (simplicialDiagonalFunctor.map (fixedSInnerCoreDiagramIso 1 r X).inv ≫
    simplicialDiagonalFunctor.map (fixedSCoreDiagramSwapIso 1 r X).hom ≫
    simplicialDiagonalFunctor.map (fixedSOneOuterCoreDiagramIso r X).hom) ≫
      simplicialDiagonalFunctor.map (oneDirectionDiagonalComparison r X) = _
  have hm : simplicialDiagonalFunctor.map
      (Functor.whiskerLeft (multiIndexDiagonal r)
        ((multiCoreSConstructionFunctor r).map (stableSOneComparison X))) =
      (multiRealizationFunctor r).map (stableSOneComparison X) := by
    rfl
  rw [← hm]
  simpa only [Functor.map_comp, Category.assoc] using congrArg simplicialDiagonalFunctor.map h

end SerrePositivity.KST.SConstruction
