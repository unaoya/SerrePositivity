module
public import SerrePositivity.KST.SConstruction.MultiMovingSInterchange
public import SerrePositivity.KST.SConstruction.DiagonalSCyclicInterchange

/-! # 全多次数の巡回交換の core と既存の実現の比較
概要：最内側の S と最外側の S の全方向交換を core へ移し、既存の全対角の交換を回収する。
方針：完全関手を core で評価し、対角の成分を既存の反復交換と照合する。
規約：元の全多次数と全対角の写像を保つ。使われ方：標的の全零境界の保存。
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

/-- 先頭添字の S が最内側にある全多単体的 core 図式。 -/
def multiInnerSCoreConstruction (r : ℕ) (X : StableModel.{u}) :
    (Fin (r + 1) → SimplexCategoryᵒᵖ) ⥤ SSet.{u} :=
  multiInnerSEndofunctor r ⋙ stableEndofunctorCoreEvaluation X

/-- 最外側の S を明示した全多単体的 core 図式と元の図式の恒等成分の同型。 -/
def multiOuterSCoreIso (r : ℕ) (X : StableModel.{u}) :
    (multiTailSEndofunctor r ⊗ multiHeadSEndofunctor r) ⋙
        stableEndofunctorCoreEvaluation X ≅ multiCoreSConstruction (r + 1) X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro d e f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    let H := stableModelForget.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor
    change H.map ((((multiTailSEndofunctor r).map f ⊗ₘ
      (multiHeadSEndofunctor r).map f)).app X) =
      H.map (((multiSEndofunctor (r + 1)).map f).app X)
    congr 1
    rw [endofunctorMonoidalCategory_tensorMap_app]
    rfl)

/-- 全多次数で最内側の S を最外側へ移す元の core 図式の自然同型。 -/
def multiMovingSCoreIso (r : ℕ) (X : StableModel.{u}) :
    multiInnerSCoreConstruction r X ≅ multiCoreSConstruction (r + 1) X :=
  Functor.isoWhiskerRight (multiMovingSInterchangeNatIso r)
    (stableEndofunctorCoreEvaluation X) ≪≫ multiOuterSCoreIso r X

/-- 内側 S の全多次数 core 図式の対角と既存の単体的 core 図式の同型。 -/
def multiInnerSCoreDiagonalIso (r : ℕ) (X : StableModel.{u}) :
    multiIndexDiagonal (r + 1) ⋙ multiInnerSCoreConstruction r X ≅
      diagonalInnerSCoreDiagram r X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro d e f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl)

/-- 既存の反復実現と最内側 S を独立な先頭添字にした図式の全対角の同型。 -/
def iteratedSMultiInnerRealizationIso (r : ℕ) (X : StableModel.{u}) :
    iteratedSRealization r X ≅
      simplicialDiagonalFunctor.obj (multiIndexDiagonal (r + 1) ⋙
        multiInnerSCoreConstruction r X) :=
  iteratedSRealizationInnerIso r X ≪≫
    (simplicialDiagonalFunctor.mapIso (multiInnerSCoreDiagonalIso r X)).symm

/-- 全多次数の交換の実現は、既存の巡回交換の実現と厳密に一致する。 -/
lemma multiMovingSCoreIso_realization (r : ℕ) (X : StableModel.{u}) :
    (iteratedSMultiInnerRealizationIso r X).hom ≫ simplicialDiagonalFunctor.map
      (Functor.whiskerLeft (multiIndexDiagonal (r + 1)) (multiMovingSCoreIso r X).hom) =
        (iteratedSRealizationCyclicIso r X).hom := by
  apply NatTrans.ext
  funext d
  let H := stableModelForget.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor
  change (H.map ((multiFixedSEndofunctorIso d.unop.len r (fun _ => d)).hom.app X)).app d =
    (H.map (((diagonalFixedSInterchangeNatIso d.unop.len r).hom.app d).app X)).app d
  rw [multiFixedSEndofunctorIso_diagonal_app]

end SerrePositivity.KST.SConstruction
