module

public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDensityRestrictedHomotopy
public import SerrePositivity.InfinityCategories.F2.ConstantTransformationVertex

/-!
概要：評価された元の密度変換を、始点固定の共同 Hom の変換の頂点へ厳密に同定する。
方針：同じ円柱の等式を変換空間の頂点に戻す。
規約：変換の像や余錐を選び直さず、全変換の指定頂点を比較する。
使われ方：元の写像空間比較の底変換自然性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の定値標的へのホモトピーの指定頂点の円柱は元の円柱。 -/
lemma homotopyTransformationVertex_prism {K X : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}
    (H : SSet.Homotopy f (SSet.const z)) :
    F2.constantTransformationPrism (SSet.yonedaEquiv.symm (homotopyTransformationVertex H)) =
      fst (K ⊗ (Δ[1] : SSet.{u})) Δ[0] ≫ H.h := by
  rw [F2.constantTransformationPrism_vertex, homotopyTransformationVertex_h]

variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)

/-- 同じ共同 Hom の全変換の始点固定を、指定された変換頂点として保持する。 -/
def presheafDensityRestrictedTransformationVertex :=
  homotopyTransformationVertex (presheafDensityRestrictedHomotopy F x)

/-- 元の大域密度変換の評価は、同じ共同 Hom 変換の始点固定そのもの。 -/
lemma presheafDensityEvaluatedTransformationVertex_restriction :
    presheafDensityEvaluatedTransformationVertex F x =
      presheafDensityRestrictedTransformationVertex F x := by
  apply SSet.yonedaEquiv.symm.injective
  apply F2.constantTransformationPrism_injective
  change F2.constantTransformationPrism (SSet.yonedaEquiv.symm
    ((F2.constantTransformationPost (presheafElementsYonedaDiagram F) (functorVertex F)
      (presheafInfinityEvaluation x)).app (Opposite.op ⦋0⦌)
        (homotopyTransformationVertex (presheafDensityDiagramHomotopy F)))) = _
  rw [← SSet.yonedaEquiv_symm_comp, F2.constantTransformationPost_prism,
    homotopyTransformationVertex_prism]
  change _ = F2.constantTransformationPrism (SSet.yonedaEquiv.symm
    (homotopyTransformationVertex (presheafDensityRestrictedHomotopy F x)))
  rw [homotopyTransformationVertex_prism, Category.assoc,
    presheafDensityDiagramHomotopy_evaluation]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
