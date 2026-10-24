module
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInitialEvaluation
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPostLaws
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorOverPrecomposition
public import SerrePositivity.InfinityCategories.F1B.Fibrations.CocartesianSectionsPrecomposition

/-! # 同じ底上の左 fibration への後合成による、元の全 section の自然な比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.Fibration
variable {E T B : SSet.{u}} (p : E ⟶ B) (q : T ⟶ B) [LeftFibration q]
  (f : E ⟶ T) (hf : f ≫ q = p)

/-- 元の全 section を後合成する。左 fibration では同じ像の全辺が cocartesian になる。 -/
def sectionPostToLeftFibration {A : SSet.{u}} (a : A ⟶ B) :
    SerrePositivity.InfinityCategories.cocartesianSections p a ⟶ SerrePositivity.InfinityCategories.cocartesianSections q a :=
  fullSubcomplexLift _ (SerrePositivity.InfinityCategories.cocartesianSectionsι p a ≫ relativeFunctorPost p q f hf a)
    (fun _ _ => isCocartesianEdge_of_leftFibration q _)

/-- 元の相対関手空間への包含は、同じ後合成を全単体で回収する。 -/
theorem sectionPostToLeftFibration_ι {A : SSet.{u}} (a : A ⟶ B) :
    sectionPostToLeftFibration p q f hf a ≫ SerrePositivity.InfinityCategories.cocartesianSectionsι q a =
      SerrePositivity.InfinityCategories.cocartesianSectionsι p a ≫ relativeFunctorPost p q f hf a := rfl

omit [LeftFibration q] in
/-- 同じ底上の前合成と後合成は、全相対関手空間上で厳密に可換。 -/
theorem relativeFunctorPost_overPre {a b : Over B} (i : a ⟶ b) :
    relativeFunctorPost p q f hf b.hom ≫ relativeFunctorOverPre q i =
      relativeFunctorOverPre p i ≫ relativeFunctorPost p q f hf a.hom := by
  apply vertexFiber_hom_ext ((ihom a.left).map q) (functorVertex a.hom)
  rw [Category.assoc, relativeFunctorOverPre_ι, ← Category.assoc, relativeFunctorPost_ι,
    Category.assoc, (pre i.left).naturality f,
    ← Category.assoc, ← relativeFunctorOverPre_ι]
  exact (congrArg (fun m => relativeFunctorOverPre p i ≫ m)
    (relativeFunctorPost_ι p q f hf a.hom)).symm.trans (Category.assoc _ _ _).symm

/-- 元の cocartesian section の全図式の前後合成も厳密に可換。 -/
theorem sectionPostToLeftFibration_overPre {a b : Over B} (i : a ⟶ b) :
    sectionPostToLeftFibration p q f hf b.hom ≫ SerrePositivity.InfinityCategories.cocartesianSectionsPre q i =
      SerrePositivity.InfinityCategories.cocartesianSectionsPre p i ≫ sectionPostToLeftFibration p q f hf a.hom := by
  apply (cancel_mono (SerrePositivity.InfinityCategories.cocartesianSectionsι q a.hom)).mp
  have he : relativeFunctorPost p q f hf b.hom ≫ SerrePositivity.InfinityCategories.relativeFunctorOverPre q i =
      SerrePositivity.InfinityCategories.relativeFunctorOverPre p i ≫ relativeFunctorPost p q f hf a.hom :=
    relativeFunctorPost_overPre p q f hf i
  rw [Category.assoc, SerrePositivity.InfinityCategories.cocartesianSectionsPre_ι, ← Category.assoc,
    sectionPostToLeftFibration_ι, Category.assoc]
  have hr : (SerrePositivity.InfinityCategories.cocartesianSectionsPre p i ≫ sectionPostToLeftFibration p q f hf a.hom) ≫
      SerrePositivity.InfinityCategories.cocartesianSectionsι q a.hom =
      SerrePositivity.InfinityCategories.cocartesianSectionsι p b.hom ≫
        (SerrePositivity.InfinityCategories.relativeFunctorOverPre p i ≫ relativeFunctorPost p q f hf a.hom) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun m => SerrePositivity.InfinityCategories.cocartesianSectionsPre p i ≫ m)
        (sectionPostToLeftFibration_ι p q f hf a.hom)).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun m => m ≫ relativeFunctorPost p q f hf a.hom)
              (SerrePositivity.InfinityCategories.cocartesianSectionsPre_ι p i)).trans (Category.assoc _ _ _))))
  exact (congrArg (fun m => SerrePositivity.InfinityCategories.cocartesianSectionsι p b.hom ≫ m) he).trans hr.symm

end SerrePositivity.KST.Fibration
