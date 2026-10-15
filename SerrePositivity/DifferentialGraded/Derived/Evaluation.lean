module
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # 導来加群圏の評価・ホモロジーと局所化による準同型判定

既存 DerivedCategory の射宇宙は HasDerivedCategory.{w} により明示的に選ぶ。
準同型判定を証明するだけの箇所には選択を要求しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 加群の各対象・整数次数での通常ホモロジー。 -/
def moduleHomology (x : D) (i : ℤ) : ModuleCategory A D ⥤ ModuleCat A :=
  moduleEvaluation A D x ⋙ HomologicalComplex.homologyFunctor (ModuleCat A) (.up ℤ) i

lemma moduleHomology_inverts (x : D) (i : ℤ) :
    (moduleQuasiIso A D).IsInvertedBy (moduleHomology A D x i) := by
  intro M N f hf
  have : QuasiIso ((moduleEvaluation A D x).map f) := hf x
  change IsIso (homologyMap ((moduleEvaluation A D x).map f) i)
  infer_instance

/-- 指定局所化の普遍性による導来加群の評価ホモロジー。 -/
def moduleDerivedHomology (x : D) (i : ℤ) : DerivedModuleCategory A D ⥤ ModuleCat A :=
  moduleDerivedLift A D (moduleHomology A D x i) (moduleHomology_inverts A D x i)

lemma moduleDerivedHomology_fac (x : D) (i : ℤ) :
    moduleToDerived A D ⋙ moduleDerivedHomology A D x i = moduleHomology A D x i :=
  moduleDerivedLift_fac A D _ _

/-- 局所化で同型になる元の射はちょうど指定 objectwise quasiIso。
ホモロジー関手への延長が逆向きを検出する。 -/
lemma moduleToDerived_map_isIso_iff {M N : ModuleCategory A D} (f : M ⟶ N) :
    IsIso ((moduleToDerived A D).map f) ↔ moduleQuasiIso A D f := by
  constructor
  · intro hf x
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have : IsIso ((moduleToDerived A D).map f) := hf
    have hmap : IsIso ((moduleDerivedHomology A D x i).map ((moduleToDerived A D).map f)) :=
      (moduleDerivedHomology A D x i).map_isIso _
    change IsIso ((moduleToDerived A D ⋙ moduleDerivedHomology A D x i).map f) at hmap
    rw [moduleDerivedHomology_fac] at hmap
    exact hmap
  · intro hf
    exact moduleToDerived_inverts A D f hf

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 元の加群評価を既存 DerivedCategory の指定局所化へ合成する。 -/
def moduleEvaluationToDerived (x : D) : ModuleCategory A D ⥤ DerivedCategory (ModuleCat A) :=
  moduleEvaluation A D x ⋙ DerivedCategory.Q

lemma moduleEvaluationToDerived_inverts (x : D) :
    (moduleQuasiIso A D).IsInvertedBy (moduleEvaluationToDerived A D x) := by
  intro M N f hf
  have : QuasiIso ((moduleEvaluation A D x).map f) := hf x
  change IsIso (DerivedCategory.Q.map ((moduleEvaluation A D x).map f))
  infer_instance

/-- 導来加群を各対象で既存の A 複体導来圏へ評価する。 -/
def moduleDerivedEvaluation (x : D) : DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat A) :=
  moduleDerivedLift A D (moduleEvaluationToDerived A D x)
    (moduleEvaluationToDerived_inverts A D x)

lemma moduleDerivedEvaluation_fac (x : D) :
    moduleToDerived A D ⋙ moduleDerivedEvaluation A D x = moduleEvaluationToDerived A D x :=
  moduleDerivedLift_fac A D _ _

end SerrePositivity.DifferentialGraded
