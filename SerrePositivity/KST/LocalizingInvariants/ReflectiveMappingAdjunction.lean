module

public import SerrePositivity.KST.LocalizingInvariants.AdjunctionOfOpposite
public import SerrePositivity.KST.LocalizingInvariants.RelativeInitialAdjunction
public import SerrePositivity.InfinityCategories.HomotopyLimits.IntervalFunctorOpposite

/-!
概要：可逆な余単位候補と、その右随伴像への元の写像空間比較から実随伴を得る。
方針：反対圏の可逆な指定単位に F1B の局所随伴判定を適用して戻す。
規約：三角恒等式は結論で構成する。使われ方：Tamme Prop. 11 の差の実随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.F1B
namespace SerrePositivity.KST.LocalizingInvariants

def oppositeFunctorIso {A D : SSet.{u}} [Quasicategory D] {F G : A ⟶ D}
    (e : FunctorIso F G) : FunctorIso (SSet.opFunctor.map G) (SSet.opFunctor.map F) where
  hom := SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv F G e.hom
  inv := SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv G F e.inv
  hom_inv_id := by
    rw [← SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv_comp, e.inv_hom_id, oppositeFunctorHom_id]
  inv_hom_id := by
    rw [← SerrePositivity.InfinityCategories.F1B.functorOppositeHomEquiv_comp, e.hom_inv_id, oppositeFunctorHom_id]

variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  {F : X ⟶ Y} {G : Y ⟶ X}

def reflectiveOppositeUnit (e : FunctorIso (G ≫ F) (𝟙 Y)) :
    FunctorIso (𝟙 Y.op) (SSet.opFunctor.map G ≫ SSet.opFunctor.map F) := by
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
    oppositeFunctorIso e

lemma unitCondition_of_iso_localMapping (η : FunctorHom (𝟙 X) (F ≫ G)) [IsIso η]
    (h : ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌), IsSimplicialHomotopyEquivalence
      (pinchedHomMap G (F.app (Opposite.op ⦋0⦌) x) y)) :
    UnitMappingSpaceCondition η := by
  intro x y
  rw [unitPinchedMap_formula]
  have : IsIso (qcatUnitComponent η x) := by
    change IsIso (functorHomEvaluate η x)
    infer_instance
  exact ((h x y).isQCatEquivalence.comp
    (PinchedPrecompose.isQCatEquivalence (qcatUnitComponent η x) _)
    ).isSimplicialHomotopyEquivalence

lemma reflectiveOppositeUnit_condition (e : FunctorIso (G ≫ F) (𝟙 Y))
    (h : ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌), IsSimplicialHomotopyEquivalence
      (pinchedHomMap F x (G.app (Opposite.op ⦋0⦌) y))) :
    UnitMappingSpaceCondition (reflectiveOppositeUnit e).hom := by
  apply unitCondition_of_iso_localMapping
  intro y x
  have hp := h (SSet.opObjEquiv x) (SSet.opObjEquiv y)
  have hi := hp.isQCatEquivalence.comp (SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_isQCatEquivalence
    (F.app (Opposite.op ⦋0⦌) (SSet.opObjEquiv x))
    (F.app (Opposite.op ⦋0⦌) (G.app (Opposite.op ⦋0⦌) (SSet.opObjEquiv y))))
  rw [pinchedIntervalComparison_naturality] at hi
  have ho := HomotopyLimits.intervalFunctorMap_op_isQCatEquivalence F _ _
    ((SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_isQCatEquivalence _ _).cancel_left hi)
  exact HomotopyLimits.pinchedHomMap_equivalence_of_intervalFunctorMap _ _ _ ho

/-- 元の局所比較と可逆余単位から、元の二関手の実随伴を構成する。 -/
def adjunctionOfReflectiveMapping (e : FunctorIso (G ≫ F) (𝟙 Y))
    (h : ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌), IsSimplicialHomotopyEquivalence
      (pinchedHomMap F x (G.app (Opposite.op ⦋0⦌) y))) : QCatAdjunction F G :=
  adjunctionOfOpposite (qcatAdjunctionOfUnitMappingSpaceCondition
    (reflectiveOppositeUnit e).hom (reflectiveOppositeUnit_condition e h))

end SerrePositivity.KST.LocalizingInvariants
