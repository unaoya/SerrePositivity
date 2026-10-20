module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionNerve
/-!
概要：実出力分解 nerve の入力射影の逆を、同じ実射影の厳密切断として固定する。
方針：自明 Kan fibration の実切断から構成した同じ全 ∞ 圏同値を使う。
規約：切断と射影の合成は全単体上で恒等射。使われ方：元の同じ入力像への augmentation。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 実入力射影を順方向、同じ厳密切断を逆方向とする、分解 nerve の実同値。 -/
def dgModuleFunctorResolutionSourceNerveEquivalence :
    QCatEquivalence (dgNerve R (DGModuleFunctorResolutionObject R C E F))
      (dgNerve R (DGUniverseLift.{v, max (u + 1) w} C)) := by
  let := dgModuleFunctorResolutionSourceNerve_trivialKanFibration R C E F
  exact qCatEquivalenceOfTrivialKanFibration
    (dgNerve.map (dgModuleFunctorResolutionSourceLift R C E F))
/-- 同じ実分解同値の逆は、入力射影の厳密切断。 -/
lemma dgModuleFunctorResolutionSourceNerveEquivalence_inv_hom :
    (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv ≫
      dgNerve.map (dgModuleFunctorResolutionSourceLift R C E F) = 𝟙 _ := by
  let := dgModuleFunctorResolutionSourceNerve_trivialKanFibration R C E F
  exact Classical.choose_spec (trivialKanFibration_exists_section
    (dgNerve.map (dgModuleFunctorResolutionSourceLift R C E F)))
end SerrePositivity.InfinityCategories
