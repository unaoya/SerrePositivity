module

public import SerrePositivity.InfinityCategories.F2.Ind.SectionFamilyProductBase
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorSpace

/-!
概要：元の積上の切断族を、添字の底だけを固定した相対切断へ写す。
方針：パラメータを忘れた共同図式が定値であることを、uncurry の自然性で示す。
規約：切断の全空間への射は変えず、固定する底の条件だけを移す。
使われ方：strict なパラメータ付き切断図式の大域 scaffold 比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 積の第二射影だけを保つと、元の底の図式は定値族となる。 -/
lemma sectionFamilyProductBase_snd {A D : SSet.{u}} (B : SSet.{u}) (a : A ⟶ D) :
    sectionFamilyProductBase B a ≫ (ihom A).map (snd B D) =
      SSet.const (functorVertex a) := by
  apply uncurry_injective
  rw [uncurry_natural_right, sectionFamilyProductBase, uncurry_curry,
    lift_snd, uncurry_const_functorVertex]

/-- 同じ切断族を添字の底のみ固定した相対関手へ写す。 -/
def parametrizedSectionsForget {A B D E : SSet.{u}} (p : E ⟶ B ⊗ D) (a : A ⟶ D) :
    parametrizedSections p (sectionFamilyProductBase B a) ⟶
      relativeFunctorSpace (p ≫ snd B D) a :=
  vertexFiberLift _ _ (parametrizedSectionsMap p (sectionFamilyProductBase B a)) (by
    rw [Functor.map_comp, ← Category.assoc, parametrizedSections_condition,
      Category.assoc, sectionFamilyProductBase_snd, SSet.comp_const])

/-- 全空間の内部 Hom への元の射は変わらない。 -/
lemma parametrizedSectionsForget_ι {A B D E : SSet.{u}} (p : E ⟶ B ⊗ D) (a : A ⟶ D) :
    parametrizedSectionsForget p a ≫
      vertexFiberι ((ihom A).map (p ≫ snd B D)) (functorVertex a) =
        parametrizedSectionsMap p (sectionFamilyProductBase B a) :=
  vertexFiberLift_ι _ _ _ _

/-- 同じ切断の全評価は、元の第一変数のパラメータを保つ。 -/
lemma parametrizedSectionsForget_uncurry_fst {A B D E : SSet.{u}}
    (p : E ⟶ B ⊗ D) (a : A ⟶ D) :
    relativeFunctorUncurry (parametrizedSectionsForget p a) ≫ p ≫ fst B D =
      snd A (parametrizedSections p (sectionFamilyProductBase B a)) ≫
        parametrizedSectionsProjection p (sectionFamilyProductBase B a) := by
  rw [relativeFunctorUncurry, parametrizedSectionsForget_ι,
    ← Category.assoc, ← uncurry_natural_right, parametrizedSections_condition,
    uncurry_natural_left, sectionFamilyProductBase, uncurry_curry,
    Category.assoc, lift_fst, whiskerLeft_snd]

end SerrePositivity.InfinityCategories.F2.Ind
