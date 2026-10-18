module

public import SerrePositivity.InfinityCategories.F1.RelativeFunctorEnrichedEvaluation
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorOverPrecomposition

/-!
概要：相対 Hom の豊穣評価の定義域に関する自然性。
方針：相対合成と底上の前合成の可換性を示し、curry して豊穣 Hom の作用の等式を得る。
規約：自然性は通常の射や頂点だけでなく全ての高次パラメーターで示す。
使われ方：Kerodon Corollary 5.6.0.6、strict transport の底の対象を動かした coherent な図式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：相対合成は定義域の底上の射による前合成と可換。
方針：各次数で二つの相対関手の合成を同じ入力で評価する。
規約：四つの底上の対象の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6、豊穣評価の定義域に関する自然性。 -/
lemma relativeFunctorComposition_overPre {B : SSet.{u}} {a b : Over B}
    (f : a ⟶ b) (p q : Over B) :
    relativeFunctorComposition b p q ≫ relativeFunctorOverPre q.hom f =
      relativeFunctorOverPre p.hom f ▷ _ ≫ relativeFunctorComposition a p q := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨g, h⟩
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 概要：相対 Hom の定義域の前合成は豊穣後合成の作用に関して自然。
方針：両辺を uncurry し、相対合成と底上の前合成の可換性に戻す。
規約：内部 Hom の射の等式により、全ての高次パラメーターを含める。
使われ方：Kerodon Corollary 5.6.0.6、底の通常の図式と fibration の coherent な射の整合性。 -/
lemma relativeFunctorPostHom_overPre {B : SSet.{u}} {a b : Over B}
    (f : a ⟶ b) (p q : Over B) :
    relativeFunctorPostHom b p q ≫
      (ihom (relativeFunctorSpace p.hom b.hom)).map (relativeFunctorOverPre q.hom f) =
    relativeFunctorPostHom a p q ≫
      (pre (relativeFunctorOverPre p.hom f)).app (relativeFunctorSpace q.hom a.hom) := by
  apply uncurry_injective
  rw [uncurry_natural_right, relativeFunctorPostHom, uncurry_curry]
  rw [uncurry_pre_app]
  rw [relativeFunctorPostHom, uncurry_curry]
  exact relativeFunctorComposition_overPre f p q

end SerrePositivity.InfinityCategories
