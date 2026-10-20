module

public import SerrePositivity.InfinityCategories.F2.PrismExtensionRestriction

/-!
概要：元の prism の延長空間の終点評価と始域族の制限を厳密に交換する。
方針：同じ区間の終点で同じ族を評価することを全次数で確認する。
規約：相対写像空間の底を固定。使われ方：全空間と各点の指定比較の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A C E B K : SSet.{u}} (p : E ⟶ B)
  (b : ((Δ[1] : SSet.{u}) ⊗ A) ⊗ K ⟶ B) (v : A ⊗ K ⟶ E)
  (hv : v ≫ p = (prismEndpoint 0 A ▷ K) ≫ b) (s : C ⟶ A ⊗ K)

/-- 概要：元の初期値付き prism の延長空間の終点を相対関手として評価する。
方針：元の全持ち上げを終点へ制限。
規約：元の底の終点への制限を固定。使われ方：元の指定比較の評価。 -/
def prismExtensionEndpoint :
    relativeFunctorExtensionSpace p b (prismEndpoint 0 A ▷ K) v hv ⟶
      relativeFunctorSpace p ((prismEndpoint 1 A ▷ K) ≫ b) :=
  relativeFunctorExtensionSpaceι p b (prismEndpoint 0 A ▷ K) v hv ≫
    relativeFunctorPre p b (prismEndpoint 1 A ▷ K)

/-- 概要：元の終点評価後の制限と全延長の制限後の終点評価は厳密に一致する。
方針：二段の fiber の包含後で同じ全単体の評価を確認する。
規約：底上の全写像の等式。使われ方：指定同型の類の厳密な比較。 -/
lemma prismExtensionEndpoint_restrict :
    prismExtensionEndpoint p b v hv ≫
        relativeFunctorPre p ((prismEndpoint 1 A ▷ K) ≫ b) s =
      prismExtensionRestriction p b v hv s ≫
        relativeFunctorExtensionSpaceι p (prismParameterRestriction s ≫ b)
          (prismEndpoint 0 C) (s ≫ v) (by rw [Category.assoc, hv]; rfl) ≫
            relativeFunctorPre p (prismParameterRestriction s ≫ b) (prismEndpoint 1 C) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro c
  rfl

end SerrePositivity.InfinityCategories.F2
