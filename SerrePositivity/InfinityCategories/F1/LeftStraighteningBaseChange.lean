module

public import SerrePositivity.InfinityCategories.F1.TransportSimplexSectionBaseChange
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningRepresentation

/-!
概要：実際の straightening の任意の底変換との全高次の両立。
方針：共同切断の底変換同型を初頂点局所化の充満忠実性で降下して二変数を交換する。
規約：底は任意の小さい単体集合。全対象に対する一つの関手同型。
使われ方：相対表現の共同比較と、単位・余単位の自然性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 宇宙持ち上げ後も初頂点写像の底に関する自然性は厳密に成り立つ。 -/
lemma transportSimplexFirstVertexMap_ulift_naturality {B D : SSet.{u}} (k : D ⟶ B) :
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k)) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B) =
    (SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap D) ≫
      (SSet.uliftFunctor.{u + 1, u}).map k := by
  rw [← Functor.map_comp, transportSimplexFirstVertexMap_naturality, Functor.map_comp]

/-- 全 left fibrations 上の共同降下図式は任意の底変換と関手同型で両立する。 -/
def leftStraighteningSectionJointDiagram_baseChangeIso {B D : SSet.{u}} (k : D ⟶ B) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map k ≫ leftStraighteningSectionJointDiagram B)
      (leftStraighteningSectionJointDiagram D ≫
        (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}) := by
  let U := SSet.uliftFunctor.{u + 1, u}
  let t := U.map (nerveMap (transportSimplexFunctor k))
  let l := U.map (transportSimplexFirstVertexMap D)
  let P := (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u}
  have hleft : l ≫ (U.map k ≫ leftStraighteningSectionJointDiagram B) =
      t ≫ (U.map (transportSimplexFirstVertexMap B) ≫
        leftStraighteningSectionJointDiagram B) := by
    rw [← Category.assoc, ← transportSimplexFirstVertexMap_ulift_naturality k, Category.assoc]
  have e : FunctorIso
      (l ≫ (U.map k ≫ leftStraighteningSectionJointDiagram B))
      (l ≫ (leftStraighteningSectionJointDiagram D ≫ P)) :=
    eqToIso (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f)) hleft) ≪≫
      (leftStraighteningSectionJointDiagram_restrictIso B).precomp t ≪≫
      (transportSimplexSectionInfinity_baseChangeIso k).symm ≪≫
      ((leftStraighteningSectionJointDiagram_restrictIso D).postcomp P).symm
  exact (localization_pre_isFullyFaithful
    (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} D)
    ((ihom (LeftFibrationInfinity B)).obj SpaceInfinity.{u})).preimageVertexIso e

/-- 実際の coherent な分類写像は任意の底変換と全対象・全高次で両立する。 -/
def leftStraighteningInfinityMap_baseChangeIso {B D : SSet.{u}} (k : D ⟶ B) :
    FunctorIso
      (leftStraighteningInfinityMap B ≫
        (pre ((SSet.uliftFunctor.{u + 1, u}).map k)).app SpaceInfinity.{u})
      (leftFibrationInfinityBaseChange k ≫ leftStraighteningInfinityMap D) := by
  have e := (leftStraighteningSectionJointDiagram_baseChangeIso k).transpose
  rw [transposeFunctorFamily_comp, transposeFunctorFamily_pre] at e
  exact e

local instance {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 全対象の底変換同型を評価すると、実際の対象図式の底変換同型になる。 -/
def leftStraighteningInfinityDiagram_baseChangeIso {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map k ≫ leftStraighteningInfinityDiagram p)
      (leftStraighteningInfinityDiagram (pullback.snd p k)) := by
  let P := (pre ((SSet.uliftFunctor.{u + 1, u}).map k)).app SpaceInfinity.{u}
  have h₁ : functorVertex ((SSet.uliftFunctor.map k) ≫ leftStraighteningInfinityDiagram p) =
      (leftStraighteningInfinityMap B ≫ P).app (Opposite.op ⦋0⦌)
        (leftFibrationInfinityVertex p) :=
    congrArg (P.app (Opposite.op ⦋0⦌)) (leftStraighteningInfinityDiagram_vertex p)
  have h₂ : (leftFibrationInfinityBaseChange k ≫ leftStraighteningInfinityMap D).app
      (Opposite.op ⦋0⦌) (leftFibrationInfinityVertex p) =
      functorVertex (leftStraighteningInfinityDiagram (pullback.snd p k)) :=
    (congrArg ((leftStraighteningInfinityMap D).app (Opposite.op ⦋0⦌))
      (leftFibrationInfinityBaseChange_vertex k (leftFibrationObjectOf p))).trans
        (leftStraighteningInfinityDiagram_vertex (pullback.snd p k)).symm
  exact eqToIso (congrArg HomotopyCategory.mk h₁) ≪≫
    (leftStraighteningInfinityMap_baseChangeIso k).app (leftFibrationInfinityVertex p) ≪≫
      eqToIso (congrArg HomotopyCategory.mk h₂)

end SerrePositivity.InfinityCategories
