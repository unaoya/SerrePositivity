module
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedSourceModel
public import SerrePositivity.InfinityCategories.Derived.DGKappaClosedProjectiveOperations
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorShiftIso
/-!
概要：出発提示の seed だけから決まる整数 shift を同じラベル模型に定義する。
方針：既存の小さい射影的閉包の shift 添字を保持し、評価には延長の実 shift 同型を使う。
規約：後合成する dg 関手によって seed を選び直さない。全閉演算は別項目。
使われ方：16時間試作の厳密関手的な表示模型の shift 閉性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (κ : Cardinal.{u})
  (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)

def dgKappaPresentedSeedShift (c : DGCategoryPresentationCode R κ)
    (i : (dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1) (s : ℤ) :
    (dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1 :=
  (dgProjectiveClosureFamily_shift R (c.Objects R κ)
    (kappaOrdinal_countable_strict_bound hκ hreg) _ s i).choose

lemma dgKappaPresentedSeedShift_value (c : DGCategoryPresentationCode R κ)
    (i : (dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1) (s : ℤ) :
    dgKappaPresentedSeedAt R κ c (dgKappaPresentedSeedShift R κ hκ hreg c i s) =
      (dgKappaPresentedSeedAt R κ c i)⟦s⟧ := by
  unfold dgKappaPresentedSeedAt dgKappaPresentedSeedShift
  exact (dgProjectiveClosureFamily_shift R (c.Objects R κ)
    (kappaOrdinal_countable_strict_bound hκ hreg) _ s i).choose_spec

variable (D : Type u) [DGCategory R D]

def dgKappaPresentedSourceShift (X : DGKappaPresentedSourceObject R D κ) (s : ℤ) :
    DGKappaPresentedSourceObject R D κ where
  code := X.code
  seed := dgKappaPresentedSeedShift R κ hκ hreg X.code X.seed s
  arrow := X.arrow

lemma dgKappaPresentedSourceObjectMap_shift (E : Type u) [DGCategory R E]
    (F : DGFunctor R D E) (X : DGKappaPresentedSourceObject R D κ) (s : ℤ) :
    dgKappaPresentedSourceObjectMap R D κ E F (dgKappaPresentedSourceShift R κ hκ hreg D X s) =
      dgKappaPresentedSourceShift R κ hκ hreg E (dgKappaPresentedSourceObjectMap R D κ E F X) s :=
  rfl

def dgKappaPresentedSourceShiftIso (X : DGKappaPresentedSourceObject R D κ) (s : ℤ) :
    ForgetEnrichment.of (Complex R)
        (dgKappaPresentedSourceValue R D κ (dgKappaPresentedSourceShift R κ hκ hreg D X s)) ≅
      (ForgetEnrichment.of (Complex R) (dgKappaPresentedSourceValue R D κ X))⟦s⟧ :=
  ((dgModuleExtension R (X.code.Objects R κ) D X.arrow).onClosed.mapIso
    (eqToIso (dgKappaPresentedSeedShift_value R κ hκ hreg X.code X.seed s))) ≪≫
    dgModuleFunctorShiftIso R (X.code.Objects R κ) D
      (dgModuleExtension R (X.code.Objects R κ) D X.arrow) s
      (ForgetEnrichment.to (Complex R) (dgKappaPresentedSourceSeed R D κ X))

end SerrePositivity.InfinityCategories
