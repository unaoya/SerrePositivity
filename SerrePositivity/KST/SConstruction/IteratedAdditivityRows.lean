module
public import SerrePositivity.KST.SConstruction.SingleRealizationAdditivity
public import SerrePositivity.KST.SConstruction.DiagonalProducts
public import SerrePositivity.KST.SConstruction.InnerZeroBoundaryNaturality
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence

/-! # 最内側 S 図式の行ごとの加法性
概要：既存の subobject・quotient の単体的自然変換を組み合わせ、行の加法性を対角へ移す。
方針：各 S_n C 上の加法性に交換同型を前合成し、自然な元の射対を得る。
規約：帰納仮定は前段の反復加法性だけ。使われ方：全有限反復の帰納段階。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.SimplicialModel

/-- 最内側の S 図式における元の subobject・quotient の自然な射対。 -/
def iteratedSAdditivityDiagram (r : ℕ) (X : StableModel.{u}) :
    iteratedSRealizationDiagram r (cofiberStableModel X) ⟶
      iteratedSRealizationDiagram r X ⊗ iteratedSRealizationDiagram r X :=
  CartesianMonoidalCategory.lift
    (iteratedSRealizationDiagramMap r (cofiberStableSubobject X))
    (iteratedSRealizationDiagramMap r (cofiberStableQuotient X))

/-- 前段の反復加法性から、最内側 S の各行の元の射対の局所化同型を得る。 -/
lemma iteratedSAdditivityDiagram_app_localized_isIso (r : ℕ)
    (hr : ∀ X : StableModel.{u},
      IsIso (AnodyneHomotopy.anodyneQ.map (multiRealizationAdditivityMap r X)))
    (X : StableModel.{u}) (n : SimplexCategoryᵒᵖ) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((iteratedSAdditivityDiagram r X).app n)) := by
  let F := multiRealizationFunctor r
  let Q := AnodyneHomotopy.anodyneQ
  change IsIso (Q.map (CartesianMonoidalCategory.lift
    (F.map ((sEndofunctor n.unop.len).map (cofiberStableSubobject X)))
    (F.map ((sEndofunctor n.unop.len).map (cofiberStableQuotient X)))))
  rw [← sCofiberStableIso_pair]
  have := hr (sStableModel n.unop.len X)
  change IsIso (Q.map (F.map (sCofiberStableIso n.unop.len X).hom ≫
    multiRealizationAdditivityMap r (sStableModel n.unop.len X)))
  rw [Q.map_comp]
  infer_instance

/-- 最内側 S 図式の全対角における subobject・quotient の射。 -/
def iteratedSAdditivityMap (r : ℕ) (X : StableModel.{u}) :
    iteratedSRealization r (cofiberStableModel X) ⟶
      iteratedSRealization r X ⊗ iteratedSRealization r X :=
  simplicialDiagonalFunctor.map (iteratedSAdditivityDiagram r X) ≫
    (diagonalTensorIso (iteratedSRealizationDiagram r X) (iteratedSRealizationDiagram r X)).hom

/-- 全対角の加法性の比較は元の二つの反復実現の射対そのもの。 -/
lemma iteratedSAdditivityMap_eq (r : ℕ) (X : StableModel.{u}) :
    iteratedSAdditivityMap r X = CartesianMonoidalCategory.lift
      (iteratedSRealizationMap r (cofiberStableSubobject X))
      (iteratedSRealizationMap r (cofiberStableQuotient X)) :=
  diagonalTensorIso_pair _ _

/-- 前段の反復加法性から最内側 S 図式の全対角の加法性へ移る。 -/
lemma iteratedSAdditivityMap_localized_isIso (r : ℕ)
    (hr : ∀ X : StableModel.{u},
      IsIso (AnodyneHomotopy.anodyneQ.map (multiRealizationAdditivityMap r X)))
    (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (iteratedSAdditivityMap r X)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (simplicialDiagonalFunctor.map (iteratedSAdditivityDiagram r X))) :=
    SerrePositivity.BisimplicialModel.localized_diagonal_map
      (iteratedSAdditivityDiagram r X) (iteratedSAdditivityDiagram_app_localized_isIso r hr X)
  rw [iteratedSAdditivityMap, AnodyneHomotopy.anodyneQ.map_comp]
  infer_instance

end SerrePositivity.KST.SConstruction
