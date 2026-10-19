module
public import SerrePositivity.KST.SConstruction.RelativeSingleRealization
public import SerrePositivity.KST.SConstruction.IteratedAdditivityRows

/-! # 相対図式の反復実現の行と対角
概要：元の相対二評価から単体的な射対を作り、各行の加法性を全対角に移す。
方針：相対 S/cofiber 交換による行の比較と既存の対角実現定理を使う。
規約：帰納仮定は前段の全相対加法性のみ。使われ方：正の有限反復への帰納段階。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.SimplicialModel

/-- 最内側の S 図式上の相対二評価の自然な射対。 -/
def relativeIteratedSAdditivityDiagram {X : StableModel.{u}} (r : ℕ)
    (A B : ClosedStablePredicate X) :
    iteratedSRealizationDiagram r (relativeCofiberStableModel A B) ⟶
      iteratedSRealizationDiagram r (closedStableModel A) ⊗
        iteratedSRealizationDiagram r (closedStableModel B) :=
  CartesianMonoidalCategory.lift
    (iteratedSRealizationDiagramMap r (relativeCofiberSubobject A B))
    (iteratedSRealizationDiagramMap r (relativeCofiberQuotient A B))

/-- 前段の相対加法性は最内側の各 S_n 行の元の二評価に適用できる。 -/
lemma relativeIteratedSAdditivityDiagram_app_localized_isIso (r : ℕ)
    (hr : ∀ (Y : StableModel.{u}) (P Q : ClosedStablePredicate Y),
      IsIso (AnodyneHomotopy.anodyneQ.map (relativeMultiRealizationAdditivityMap r P Q)))
    {X : StableModel.{u}} (A B : ClosedStablePredicate X) (n : SimplexCategoryᵒᵖ) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((relativeIteratedSAdditivityDiagram r A B).app n)) := by
  change IsIso (AnodyneHomotopy.anodyneQ.map (CartesianMonoidalCategory.lift
    ((multiRealizationFunctor r).map
      ((sEndofunctor n.unop.len).map (relativeCofiberSubobject A B)))
    ((multiRealizationFunctor r).map
      ((sEndofunctor n.unop.len).map (relativeCofiberQuotient A B)))))
  exact relativeRowAdditivity_localized_isIso (multiRealizationFunctor r) n.unop.len A B
    (hr (sStableModel n.unop.len X) (sClosedPredicate n.unop.len A) (sClosedPredicate n.unop.len B))

/-- 最内側 S 図式の全対角の相対加法性の比較。 -/
def relativeIteratedSAdditivityMap {X : StableModel.{u}} (r : ℕ)
    (A B : ClosedStablePredicate X) :
    iteratedSRealization r (relativeCofiberStableModel A B) ⟶
      iteratedSRealization r (closedStableModel A) ⊗
        iteratedSRealization r (closedStableModel B) :=
  simplicialDiagonalFunctor.map (relativeIteratedSAdditivityDiagram r A B) ≫
    (diagonalTensorIso (iteratedSRealizationDiagram r (closedStableModel A))
      (iteratedSRealizationDiagram r (closedStableModel B))).hom

/-- 相対比較の全対角は元の二評価の反復実現の射対に一致する。 -/
lemma relativeIteratedSAdditivityMap_eq {X : StableModel.{u}} (r : ℕ)
    (A B : ClosedStablePredicate X) :
    relativeIteratedSAdditivityMap r A B = CartesianMonoidalCategory.lift
      (iteratedSRealizationMap r (relativeCofiberSubobject A B))
      (iteratedSRealizationMap r (relativeCofiberQuotient A B)) :=
  diagonalTensorIso_pair _ _

/-- 前段の相対加法性から全対角での相対加法性が従う。 -/
lemma relativeIteratedSAdditivityMap_localized_isIso (r : ℕ)
    (hr : ∀ (Y : StableModel.{u}) (P Q : ClosedStablePredicate Y),
      IsIso (AnodyneHomotopy.anodyneQ.map (relativeMultiRealizationAdditivityMap r P Q)))
    {X : StableModel.{u}} (A B : ClosedStablePredicate X) :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeIteratedSAdditivityMap r A B)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (simplicialDiagonalFunctor.map (relativeIteratedSAdditivityDiagram r A B))) :=
    SerrePositivity.BisimplicialModel.localized_diagonal_map
      (relativeIteratedSAdditivityDiagram r A B)
      (relativeIteratedSAdditivityDiagram_app_localized_isIso r hr A B)
  rw [relativeIteratedSAdditivityMap, AnodyneHomotopy.anodyneQ.map_comp]
  infer_instance

end SerrePositivity.KST.SConstruction
