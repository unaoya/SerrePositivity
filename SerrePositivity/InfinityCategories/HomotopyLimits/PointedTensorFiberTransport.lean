module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PointedTensorCoefficient
public import SerrePositivity.InfinityCategories.HomotopyLimits.TensorHomotopyEquivalence

/-!
概要：元の二射影の coherent 辺に沿う普遍 fiber の輸送の対は同値。
方針：同じ係数同型と両側の標準比較を、両射影の輸送との可換性で結ぶ。
規約：二つの元の射影辺を保持。使われ方：点ごとの積図式の全空間比較の fiber 判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
attribute [local instance] vertexFiber_kanComplex_of_leftFibration kanTensor_isKan

/-- 元の fst・snd の coherent 辺に沿う普遍輸送を組にする。 -/
def pointedTensorFiberTransport (K L : KanObject.{u}) :
    vertexFiber pointedSpaceProjection (coherentNerveVertex ((kanTensorLeft K).obj L)) ⟶
      vertexFiber pointedSpaceProjection (coherentNerveVertex K) ⊗
        vertexFiber pointedSpaceProjection (coherentNerveVertex L) :=
  lift
    (edgeTransport pointedSpaceProjection (coherentNerveEdge
      (show (kanTensorLeft K).obj L ⟶ K from fst K.obj L.obj)))
    (edgeTransport pointedSpaceProjection (coherentNerveEdge
      (show (kanTensorLeft K).obj L ⟶ L from snd K.obj L.obj)))

/-- 同じ係数同型から fiber の積への比較は、元の両射影の輸送の対と可換。 -/
def pointedTensorFiberTransportComparisonIso (K L : KanObject.{u}) :
    FunctorIso
      ((pointedTensorCoefficientIso K L).hom ≫
        (pointedCoherentFiberComparison K ⊗ₘ pointedCoherentFiberComparison L))
      (pointedCoherentFiberComparison ((kanTensorLeft K).obj L) ≫
        pointedTensorFiberTransport K L) := by
  let a : (kanTensorLeft K).obj L ⟶ K := fst K.obj L.obj
  let b : (kanTensorLeft K).obj L ⟶ L := snd K.obj L.obj
  let c := pointedCoherentFiberComparison ((kanTensorLeft K).obj L)
  let f := (SSet.uliftFunctor.{u + 1, u}).map
    (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject a))
  let g := (SSet.uliftFunctor.{u + 1, u}).map
    (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject b))
  let p := edgeTransport pointedSpaceProjection (coherentNerveEdge a)
  let q := edgeTransport pointedSpaceProjection (coherentNerveEdge b)
  have H := pairedSimplicialHomotopy
    (pointedCoherentFiberComparison_transportIso a).simplicialHomotopy
    (pointedCoherentFiberComparison_transportIso b).simplicialHomotopy
  have h₀ : lift (f ≫ pointedCoherentFiberComparison K) (g ≫ pointedCoherentFiberComparison L) =
      (pointedTensorCoefficientIso K L).hom ≫
        (pointedCoherentFiberComparison K ⊗ₘ pointedCoherentFiberComparison L) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, Category.assoc, tensorHom_fst, ← Category.assoc,
        pointedTensorCoefficientIso_fst]
    · rw [lift_snd, Category.assoc, tensorHom_snd, ← Category.assoc,
        pointedTensorCoefficientIso_snd]
  have h₁ : lift (c ≫ p) (c ≫ q) = c ≫ pointedTensorFiberTransport K L := by
    rw [pointedTensorFiberTransport, comp_lift]
  change SSet.Homotopy
    (lift (f ≫ pointedCoherentFiberComparison K) (g ≫ pointedCoherentFiberComparison L))
    (lift (c ≫ p) (c ≫ q)) at H
  rw [h₀, h₁] at H
  exact functorIsoOfSimplicialHomotopy H

/-- 元の二射影の普遍 fiber 輸送の対は同じ実際の射について同値。 -/
lemma pointedTensorFiberTransport_isQCatEquivalence (K L : KanObject.{u}) :
    IsQCatEquivalence (pointedTensorFiberTransport K L) := by
  have h := (qCatEquivalenceOfIso (pointedTensorCoefficientIso K L)).isQCatEquivalence.comp
    (tensor_isQCatEquivalence (pointedCoherentFiberComparison_isQCatEquivalence K)
      (pointedCoherentFiberComparison_isQCatEquivalence L))
  exact (pointedCoherentFiberComparison_isQCatEquivalence ((kanTensorLeft K).obj L)).cancel_left
    (h.ofFunctorIso (pointedTensorFiberTransportComparisonIso K L))

end SerrePositivity.InfinityCategories.HomotopyLimits
