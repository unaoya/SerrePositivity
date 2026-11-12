module
public import SerrePositivity.KST.SConstruction.DiagonalSInterchangeIndex
public import SerrePositivity.KST.SConstruction.FixedSRealizationSwap

/-! # 最内側の S を最外側へ動かす全対角の交換
概要：固定方向も対角次数で動かし、有限反復の最内側 S と最外側 S を自然に交換する。
方針：固定方向の自然性と残りの対角方向の自然性を合成する。
規約：全 gapped 図式上の既存の交換を使う。使われ方：区間族の標的の巡回交換。
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

/-- 固定方向も対角に動かした内外 S 交換の自然同型。 -/
def diagonalSCyclicInterchangeNatIso (r : ℕ) :
    simplicialStableEndofunctor.{u} ⊗ diagonalSEndofunctor r ≅
      diagonalSEndofunctor r ⊗ simplicialStableEndofunctor :=
  NatIso.ofComponents (fun d => (diagonalFixedSInterchangeNatIso d.unop.len r).app d) (by
    intro d e f
    apply NatTrans.ext
    funext X
    let F := diagonalSEndofunctor.{u} r
    let a := (simplicialStableEndofunctor.map f)
    have hf := NatTrans.congr_app
      ((diagonalFixedSInterchangeNatIso d.unop.len r).hom.naturality f) X
    have hi := diagonalFixedSInterchangeNatIso_index r e X f.unop.toOrderHom
    have ha := a.naturality ((F.map f).app X)
    change (((𝟙 (sEndofunctor d.unop.len) ⊗ₘ F.map f) ≫
      (diagonalFixedSInterchangeNatIso d.unop.len r).hom.app e).app X) =
        (((diagonalFixedSInterchangeNatIso d.unop.len r).hom.app d ≫
          (F.map f ⊗ₘ 𝟙 (sEndofunctor d.unop.len))).app X) at hf
    simp only [NatTrans.comp_app, endofunctorMonoidalCategory_tensorMap_app,
      NatTrans.id_app, CategoryTheory.Functor.map_id, Category.comp_id] at hf
    change (F.map f).app ((sEndofunctor d.unop.len).obj X) ≫
        ((diagonalFixedSInterchangeNatIso d.unop.len r).hom.app e).app X =
      ((diagonalFixedSInterchangeNatIso d.unop.len r).hom.app d).app X ≫
        (𝟙 _ ≫ (sEndofunctor d.unop.len).map ((F.map f).app X)) at hf
    rw [Category.id_comp] at hf
    change (((simplicialStableEndofunctor.map f ⊗ₘ F.map f) ≫
      (diagonalFixedSInterchangeNatIso e.unop.len r).hom.app e).app X) =
        (((diagonalFixedSInterchangeNatIso d.unop.len r).hom.app d ≫
          (F.map f ⊗ₘ simplicialStableEndofunctor.map f)).app X)
    simp only [NatTrans.comp_app, endofunctorMonoidalCategory_tensorMap_app]
    change ((F.map f).app ((sEndofunctor d.unop.len).obj X) ≫ (F.obj e).map (a.app X)) ≫
      ((diagonalFixedSInterchangeNatIso e.unop.len r).hom.app e).app X =
      ((diagonalFixedSInterchangeNatIso d.unop.len r).hom.app d).app X ≫
        (a.app ((F.obj d).obj X) ≫ (sEndofunctor e.unop.len).map ((F.map f).app X))
    have hi' : (F.obj e).map (a.app X) ≫
        ((diagonalFixedSInterchangeNatIso e.unop.len r).hom.app e).app X =
      ((diagonalFixedSInterchangeNatIso d.unop.len r).hom.app e).app X ≫
        a.app ((F.obj e).obj X) := hi
    change (sEndofunctor d.unop.len).map ((F.map f).app X) ≫ a.app ((F.obj e).obj X) =
      a.app ((F.obj d).obj X) ≫ (sEndofunctor e.unop.len).map ((F.map f).app X) at ha
    rw [Category.assoc, hi', ← Category.assoc, hf, Category.assoc]
    exact congrArg
      (fun h => ((diagonalFixedSInterchangeNatIso d.unop.len r).hom.app d).app X ≫ h) ha)

/-- 全対角の core 図式で最内側の S を最外側へ移す自然同型。 -/
def diagonalSCyclicCoreIso (r : ℕ) (X : StableModel.{u}) :
    diagonalInnerSCoreDiagram r X ≅
      (diagonalSEndofunctor r ⊗ simplicialStableEndofunctor) ⋙
        stableEndofunctorCoreEvaluation X :=
  Functor.isoWhiskerRight (diagonalSCyclicInterchangeNatIso r)
    (stableEndofunctorCoreEvaluation X)

/-- 最外側の S を明示した core 図式は、元の反復 core 図式と恒等成分で同型。 -/
def diagonalOuterSCoreDiagramIso (r : ℕ) (X : StableModel.{u}) :
    (diagonalSEndofunctor r ⊗ simplicialStableEndofunctor) ⋙
        stableEndofunctorCoreEvaluation X ≅
      diagonalSEndofunctor (r + 1) ⋙ stableEndofunctorCoreEvaluation X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro d e f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    let H := stableModelForget.{u} ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor
    change H.map (((diagonalSEndofunctor r ⊗ simplicialStableEndofunctor).map f).app X) =
      H.map (((diagonalSEndofunctor (r + 1)).map f).app X)
    congr 1
    change (((diagonalSEndofunctor r).map f ⊗ₘ simplicialStableEndofunctor.map f).app X) = _
    rw [endofunctorMonoidalCategory_tensorMap_app]
    rfl)

/-- 全対角の最内側の S を最外側へ移す元の core 実現の同型。 -/
def iteratedSRealizationCyclicIso (r : ℕ) (X : StableModel.{u}) :
    iteratedSRealization r X ≅ multiDiagonalCoreSConstruction (r + 1) X :=
  iteratedSRealizationInnerIso r X ≪≫
    simplicialDiagonalFunctor.mapIso (diagonalSCyclicCoreIso r X) ≪≫
    simplicialDiagonalFunctor.mapIso (diagonalOuterSCoreDiagramIso r X)

end SerrePositivity.KST.SConstruction
