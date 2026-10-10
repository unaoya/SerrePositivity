module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TExact

/-!
# 完全関手から誘導される導来関手の t 完全性

標準 t 構造の片側有界な複体による表示を用いる。
元のアーベル圏の完全関手以外に、切り詰めの保存を仮定しない。
-/

@[expose] public section

universe w₁ w₂

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

variable {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [Category* B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- 完全関手の導来関手は標準 t 構造に関して右 t 完全。 -/
instance exactDerived_rightTExact :
    F.mapDerivedCategory.RightTExact DerivedCategory.TStructure.t DerivedCategory.TStructure.t :=
  Functor.RightTExact.mk _ _ _ (by
    intro X hX
    obtain ⟨K, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE X 0
    exact ⟨⟨(F.mapHomologicalComplex _).obj K,
      F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app K,
      inferInstance⟩⟩)

/-- 完全関手の導来関手は標準 t 構造に関して左 t 完全。 -/
instance exactDerived_leftTExact :
    F.mapDerivedCategory.LeftTExact DerivedCategory.TStructure.t DerivedCategory.TStructure.t :=
  Functor.LeftTExact.mk _ _ _ (by
    intro X hX
    obtain ⟨K, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE X 0
    exact ⟨⟨(F.mapHomologicalComplex _).obj K,
      F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app K,
      inferInstance⟩⟩)

/-- 完全関手の導来関手は標準 t 構造に関して t 完全。 -/
instance exactDerived_tExact :
    F.mapDerivedCategory.TExact DerivedCategory.TStructure.t DerivedCategory.TStructure.t := {}

/-- 完全関手の導来関手による像のホモロジーの比較。 -/
noncomputable def exactDerivedHomologyIso (X : DerivedCategory A) (n : ℤ) :
    (DerivedCategory.homologyFunctor B n).obj (F.mapDerivedCategory.obj X) ≅
      F.obj ((DerivedCategory.homologyFunctor A n).obj X) := by
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  exact (DerivedCategory.homologyFunctor B n).mapIso
      (F.mapDerivedCategory.mapIso e.symm ≪≫ F.mapDerivedCategoryFactors.app K) ≪≫
    (DerivedCategory.homologyFunctorFactors B n).app _ ≪≫
    (K.sc n).mapHomologyIso F ≪≫
    F.mapIso (((DerivedCategory.homologyFunctorFactors A n).app K).symm ≪≫
      (DerivedCategory.homologyFunctor A n).mapIso e)

/-- 導来圏の零対象は全ホモロジーの消滅で判定できる。 -/
lemma derived_isZero_iff_homology (X : DerivedCategory A) :
    IsZero X ↔ ∀ n : ℤ, IsZero ((DerivedCategory.homologyFunctor A n).obj X) := by
  refine ⟨fun h n ↦ (DerivedCategory.homologyFunctor A n).map_isZero h, fun h ↦ ?_⟩
  have hi : IsIso (0 : X ⟶ X) := (DerivedCategory.isIso_iff A _).2 (fun n ↦ by
    rw [Functor.map_zero]
    exact (h n).isIso (h n) _)
  exact ((isIsoZero_iff_source_target_isZero X X).1 hi).1

/-- 導来関手の核は、全ホモロジーが元の完全関手の核に入る対象。 -/
lemma exactDerived_isZero_iff (X : DerivedCategory A) :
    IsZero (F.mapDerivedCategory.obj X) ↔
      ∀ n : ℤ, IsZero (F.obj ((DerivedCategory.homologyFunctor A n).obj X)) := by
  rw [derived_isZero_iff_homology]
  exact forall_congr' (fun n ↦ (exactDerivedHomologyIso F X n).isZero_iff)

end SerrePositivity
