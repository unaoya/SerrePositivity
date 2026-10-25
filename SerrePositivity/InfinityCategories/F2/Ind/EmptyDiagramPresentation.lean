module

public import SerrePositivity.InfinityCategories.F2.Ind.EmptyDiagramCommaFamily
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramFilteredPresentation

/-!
概要：元の空形状の図式そのものは、同じ小さい comma による単一 filtered 表示を持つ。
方針：任意の元の試験族の実余錐を小さい模型へ戻し、各点条件は頂点非存在で検査する。
規約：κ の正則性や C の対象の存在を追加仮定にしない。
使われ方：有限半順序形状の filtered 性と各点密度の帰納の基底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C) (hK : ¬ K.Nonempty)
include hK
/-- 概要：元の空形状の小さい実表示 comma は κ-filtered。
方針：持ち上げた全族の実余錐を降下。規約：元の添字。使われ方：空の帰納基底。 -/
lemma smallDiagramComma_isKappaFiltered_of_empty_shape :
    IsKappaFiltered κ (smallDiagramComma κ D) := by
  constructor
  intro A hA f
  let q := (SSet.uliftFunctor.{u + 1, u}).map f ≫ (smallDiagramCommaIso κ D).hom
  obtain ⟨c⟩ := nonempty_emptyDiagramComma_cocone κ D hK q
  have hc : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map f) := by
    simpa only [q, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      mapJoinCocone (smallDiagramCommaIso κ D).inv c
  obtain ⟨d, _⟩ := JoinCocone.ulift_surjective.{u, u + 1} f hc
  exact ⟨d⟩
/-- 概要：元の空全図式自身に、同じ小さい filtered 表示が存在する。
方針：各点条件は空。規約：同じ D を頂点とする。使われ方：表示の帰納の基底。 -/
lemma indEmpty_has_singleFilteredDiagramPresentation : HasSingleFilteredDiagramPresentation κ D :=
  hasSingleFilteredDiagramPresentation_of_evaluation_cofinal κ D
    (smallDiagramComma_isKappaFiltered_of_empty_shape κ D hK)
    (fun k ↦ False.elim (hK ⟨k⟩))
end SerrePositivity.InfinityCategories.F2.Ind
