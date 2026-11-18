module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductSectionsHomEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedWeightSectionMap

/-!
# 指定 A09 比較の全標準単体での uncurry

概要：元のAW比較を同じ自由随伴と指定AW前合成で全パラメータに評価する。
方針：元のtensor Hom同型の逆射則と積重みHomのuncurry則を合成する。
規約：既存構成の法則。入力は同じ全Hom単体を尽くす。
使われ方：HA 1.2.4、IS-W2 B02の実豊穣合成との指定射の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (A : Type u) [CommRing A] {J : Type u} [SmallCategory J]

/-- 概要：同じA09の全単体の像を指定AW前合成の自由随伴で計算する。
方針：元のtensor Hom同型を消去して積側の指定uncurry則を使う。
規約：φと重み・全パラメータを保持。使われ方：HA 1.2.4 の指定射の比較。 -/
theorem normalizedWeightSectionMap_hom_uncurry (W : J ⥤ SSet.{u})
    (Q : J ⥤ Complex A) (φ : simplicialRingCoefficient.{u} →+* A) (n : SimplexCategory)
    (f : (freeTensorFrame A W (liftedStandardSimplexParameter J)).obj n ⟶ Q) :
    weightedSectionsUncurry
      (liftedStandardSimplexIso.{u}.hom.app n ≫ SSet.yonedaEquiv.symm
        ((normalizedWeightSectionMap A W Q φ).app (Opposite.op n)
          ((freeTensorDiagramHomIso.{u,u} A Q W).hom.app (Opposite.op n) f))) =
    (freeNegativeChainsDiagramAdjunction A J).homEquiv
      (W ⊗ (Functor.const J).obj
        ((SSet.uliftFunctor.{u,0}).obj (SSet.stdSimplex.{0}.obj n))) Q
      (freeProductDiagramAW φ W ((liftedStandardSimplexParameter J).obj n) ≫ f) := by
  have hi := ConcreteCategory.congr_hom
    (Iso.hom_inv_id_app (freeTensorDiagramHomIso.{u,u} A Q W) (Opposite.op n)) f
  change (freeTensorDiagramHomIso.{u,u} A Q W).inv.app (Opposite.op n)
    ((freeTensorDiagramHomIso.{u,u} A Q W).hom.app (Opposite.op n) f) = f at hi
  have he : (normalizedWeightSectionMap A W Q φ).app (Opposite.op n)
        ((freeTensorDiagramHomIso.{u,u} A Q W).hom.app (Opposite.op n) f) =
      (freeProductSectionsHomIso A W Q).hom.app (Opposite.op n)
        (freeProductDiagramAW φ W ((liftedStandardSimplexParameter J).obj n) ≫ f) := by
    change (freeProductSectionsHomIso A W Q).hom.app (Opposite.op n)
      (((freeProductHomComparison A W (liftedStandardSimplexParameter J) φ).app Q).app
        (Opposite.op n) ((freeTensorDiagramHomIso.{u,u} A Q W).inv.app (Opposite.op n)
          ((freeTensorDiagramHomIso.{u,u} A Q W).hom.app (Opposite.op n) f))) = _
    rw [hi, freeProductHomComparison_apply]
  rw [he]
  exact freeProductSectionsHomIso_uncurry A W Q n _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
