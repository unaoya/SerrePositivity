module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeCoproduct
/-!
概要：非可算正則 κ の自由表示模型に可算直和を指定する。
方針：ordinal の列だけから一度平坦化を選び、各対象ラベルへ同じ選択を使う。
規約：対象写像との可換性は厳密等式、評価との比較は全加群同型である。
使われ方：16時間試作の可算閉演算。cone の閉性や全被覆は別項目。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)

def dgKappaFreeCountableShape (a : ℕ → κ.ord.ToType) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaFreeSumShape (fun n : ULift.{u} ℕ => a n.down) :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaFreeSumShape_nonempty _ hreg (by simpa using hκ))

variable {R : Type u} [CommRing R] {D : Type v} {E : Type w}
  [DGCategory R D] [DGCategory R E] [Small.{u} D] [Small.{u} E]

def dgKappaPresentedFreeCountable (X : ℕ → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeSum (fun n : ULift.{u} ℕ => X n.down)
    (dgKappaFreeCountableShape hκ hreg (fun n => (X n).label.1))

lemma dgKappaPresentedFreeObjectMap_countable (F : DGFunctor R D E)
    (X : ℕ → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeObjectMap R F (dgKappaPresentedFreeCountable hκ hreg X) =
      dgKappaPresentedFreeCountable hκ hreg
        (fun n => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeObjectMap R F (X n)) := rfl

def dgKappaPresentedFreeCountableIso (X : ℕ → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) :
    ForgetEnrichment.of (Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R D κ (dgKappaPresentedFreeCountable hκ hreg X)) ≅
      ∐ (fun n : ℕ => ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R D κ (X n))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeSumIso _ _ ≪≫ Sigma.whiskerEquiv
    (g := fun n : ℕ => ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R D κ (X n)))
    Equiv.ulift (fun _ => Iso.refl _)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
