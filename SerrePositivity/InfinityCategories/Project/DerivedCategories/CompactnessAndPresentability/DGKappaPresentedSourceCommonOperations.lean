module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaPresentedSeedOperations
public import SerrePositivity.DifferentialGraded.Module.Functor
public import SerrePositivity.DifferentialGraded.Functor.ModuleValued
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
/-!
概要：同じ出発提示と arrow を持つラベルの直和と持ち上げ済み閉射の cone を評価する。
方針：seed 演算を保持し、延長の左随伴性と加群値 dg 関手の実 cone 比較を使う。
規約：任意の標的閉射の持ち上げや異なる提示間の精密化は仮定せず、別課題とする。
使われ方：共通提示への同時精密化後に必要な閉演算の実比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type u) [DGCategory R D]
  (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
  (c : DGCategoryPresentationCode R κ) (L : DGFunctor R (c.Objects R κ) D)

def dgKappaPresentedSourceAt
    (i : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ := ⟨c, i, L⟩

def dgKappaPresentedSourceCommonBinary
    (i j : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ :=
  dgKappaPresentedSourceAt R D κ c L (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedBinary R κ hκ hreg c i j)

def dgKappaPresentedSourceCommonCountable
    (i : ℕ → (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ :=
  dgKappaPresentedSourceAt R D κ c L (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedCountable R κ hκ hreg c i)

def dgKappaPresentedSourceCommonCone
    (i j : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1)
    (f : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c i ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c j) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ :=
  dgKappaPresentedSourceAt R D κ c L (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedCone R κ hκ hreg c i j f)

def dgKappaPresentedSourceCommonBinaryIso
    (i j : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1) :
    ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ
      (dgKappaPresentedSourceCommonBinary R D κ hκ hreg c L i j)) ≅
      ((dgModuleExtension R (c.Objects R κ) D L).onClosed.obj
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c i) ⨿
        (dgModuleExtension R (c.Objects R κ) D L).onClosed.obj
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c j)) := by
  let F := (dgModuleExtension R (c.Objects R κ) D L).onClosed
  letI := (dgModuleExtensionRestrictionAdjunction R (c.Objects R κ) D L).isLeftAdjoint
  exact F.mapIso (eqToIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedBinary_value R κ hκ hreg c i j)) ≪≫
    (PreservesColimitPair.iso F _ _).symm

def dgKappaPresentedSourceCommonCountableIso
    (i : ℕ → (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1) :
    ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ
      (dgKappaPresentedSourceCommonCountable R D κ hκ hreg c L i)) ≅
      ∐ (fun n => (dgModuleExtension R (c.Objects R κ) D L).onClosed.obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c (i n))) := by
  let F := (dgModuleExtension R (c.Objects R κ) D L).onClosed
  letI := (dgModuleExtensionRestrictionAdjunction R (c.Objects R κ) D L).isLeftAdjoint
  exact F.mapIso (eqToIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedCountable_value R κ hκ hreg c i)) ≪≫
    PreservesCoproduct.iso F _

def dgKappaPresentedSourceCommonConeIso
    (i j : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1)
    (f : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c i ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c j) :
    ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ
      (dgKappaPresentedSourceCommonCone R D κ hκ hreg c L i j f)) ≅
      moduleCone R D ((dgModuleExtension R (c.Objects R κ) D L).onClosed.map f) := by
  let F := dgModuleExtension R (c.Objects R κ) D L
  exact F.onClosed.mapIso (eqToIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedCone_value R κ hκ hreg c i j f)) ≪≫
    (DGFunctor.moduleValuedConeIso R (c.Objects R κ) D F f).symm

variable (E : Type u) [DGCategory R E] (F : DGFunctor R D E)

lemma dgKappaPresentedSourceObjectMap_commonBinary
    (i j : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap R D κ E F
      (dgKappaPresentedSourceCommonBinary R D κ hκ hreg c L i j) =
      dgKappaPresentedSourceCommonBinary R E κ hκ hreg c (L.comp F) i j := rfl

lemma dgKappaPresentedSourceObjectMap_commonCountable
    (i : ℕ → (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap R D κ E F
      (dgKappaPresentedSourceCommonCountable R D κ hκ hreg c L i) =
      dgKappaPresentedSourceCommonCountable R E κ hκ hreg c (L.comp F) i := rfl

lemma dgKappaPresentedSourceObjectMap_commonCone
    (i j : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1)
    (f : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c i ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt R κ c j) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap R D κ E F
      (dgKappaPresentedSourceCommonCone R D κ hκ hreg c L i j f) =
      dgKappaPresentedSourceCommonCone R E κ hκ hreg c (L.comp F) i j f := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
