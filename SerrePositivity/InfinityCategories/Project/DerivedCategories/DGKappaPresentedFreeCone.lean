module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeExtension
public import SerrePositivity.DifferentialGraded.Functor.ModuleValued
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
/-!
概要：自由表示の二対象と元の閉射を保持する、小さい cone 表示を構成する。
方針：閉射を評価前のラベルに残し、延長像を両端の実比較同型で輸送する。
規約：自由表示の一段の cone であり、反復閉性や関手変数の厳密則はまだ結論しない。
使われ方：16時間試作の cone 係数輸送と全加群比較を検証する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u})

structure DGKappaPresentedFreeConeObject where
  source : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ
  target : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ
  arrow : ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R D κ source) ⟶
    ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R D κ target)

lemma dgKappaPresentedFreeConeObject_small :
    Small.{u} (DGKappaPresentedFreeConeObject R D κ) := by infer_instance

@[irreducible] def dgKappaPresentedFreeConeValue
    (X : DGKappaPresentedFreeConeObject R D κ) : ModuleCategory R D :=
  moduleCone R D X.arrow

lemma dgKappaPresentedFreeConeValue_projective (X : DGKappaPresentedFreeConeObject R D κ) :
    moduleHomotopicallyProjective R D (dgKappaPresentedFreeConeValue R D κ X) := by
  unfold dgKappaPresentedFreeConeValue
  exact moduleHomotopicallyProjective_cone R D
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue_projective R D κ X.source)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue_projective R D κ X.target) X.arrow

variable (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R D E)

@[irreducible] def dgKappaPresentedFreeArrowMap
    {M N : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ}
    (f : ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R D κ M) ⟶
      ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R D κ N)) :
    ForgetEnrichment.of (Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R E κ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeObjectMap R F M)) ⟶
      ForgetEnrichment.of (Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R E κ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeObjectMap R F N)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeExtensionIso R D E F κ M).inv ≫
    (dgModuleExtension R D E F).onClosed.map f ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeExtensionIso R D E F κ N).hom

def dgKappaPresentedFreeConeObjectMap (X : DGKappaPresentedFreeConeObject R D κ) :
    DGKappaPresentedFreeConeObject R E κ where
  source := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeObjectMap R F X.source
  target := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeObjectMap R F X.target
  arrow := dgKappaPresentedFreeArrowMap R D κ E F (M := X.source) (N := X.target) X.arrow

/-- 同じ元の延長 cone と、両端を輸送した閉射の cone との実比較。 -/
def dgKappaPresentedFreeConeExtensionIso (X : DGKappaPresentedFreeConeObject R D κ) :=
  DGFunctor.moduleValuedConeTransportIso R D E (dgModuleExtension R D E F) X.arrow
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeExtensionIso R D E F κ X.source)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeExtensionIso R D E F κ X.target)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
