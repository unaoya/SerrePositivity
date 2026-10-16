module
public import SerrePositivity.DifferentialGraded.Perfect.FiniteCellProjective
public import SerrePositivity.DifferentialGraded.Derived.Triangulated
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # 指定導来圏内のfinite cellのretractとしてのPerf -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
open scoped ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定生成元からのfinite cellの、指定導来圏内の本質的像。 -/
def derivedFiniteCellOver (S : Set D) : ObjectProperty (DerivedModuleCategory A D) :=
  (moduleFiniteCellOver A D S).map (moduleToDerived A D)

/-- Perf_S(D)：D(D)内でfinite cellの像のretractとなる対象。 -/
def modulePerfectOver (S : Set D) : ObjectProperty (DerivedModuleCategory A D) :=
  (derivedFiniteCellOver A D S).retractClosure

/-- Perf(D)：すべての代表加群を生成元として許したperfect対象。 -/
def modulePerfect : ObjectProperty (DerivedModuleCategory A D) := modulePerfectOver A D Set.univ

/-- 同じ指定導来圏の充満部分圏としてのPerf_S(D)。 -/
abbrev PerfectModuleCategoryOver (S : Set D) := (modulePerfectOver A D S).FullSubcategory

abbrev PerfectModuleCategory := PerfectModuleCategoryOver A D Set.univ

def perfectModuleInclusion (S : Set D) :
    PerfectModuleCategoryOver A D S ⥤ DerivedModuleCategory A D :=
  (modulePerfectOver A D S).ι

instance modulePerfectOverStableUnderRetracts (S : Set D) :
    (modulePerfectOver A D S).IsStableUnderRetracts := by
  dsimp [modulePerfectOver]
  infer_instance

instance modulePerfectOverClosedUnderIso (S : Set D) :
    (modulePerfectOver A D S).IsClosedUnderIsomorphisms := inferInstance

/-- 中間の同型を吸収し、実際のfinite cellの像へのretractで判定する。 -/
lemma modulePerfectOver_iff (S : Set D) (X : DerivedModuleCategory A D) :
    modulePerfectOver A D S X ↔ ∃ M : ModuleCategory A D,
      moduleFiniteCellOver A D S M ∧ Nonempty (Retract X ((moduleToDerived A D).obj M)) := by
  constructor
  · rintro ⟨Y, ⟨M, hM, ⟨e⟩⟩, ⟨r⟩⟩
    exact ⟨M, hM, ⟨r.trans (Retract.ofIso e.symm)⟩⟩
  · rintro ⟨M, hM, ⟨r⟩⟩
    exact ObjectProperty.prop_retractClosure
      ((moduleFiniteCellOver A D S).prop_map_obj (moduleToDerived A D) hM) r

lemma modulePerfectOver_of_finiteCell {S : Set D} {M : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) : modulePerfectOver A D S ((moduleToDerived A D).obj M) :=
  (derivedFiniteCellOver A D S).le_retractClosure _
    ((moduleFiniteCellOver A D S).prop_map_obj (moduleToDerived A D) hM)

lemma modulePerfectOver_representable {S : Set D} (x : D) (hx : x ∈ S) :
    modulePerfectOver A D S ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x))) :=
  modulePerfectOver_of_finiteCell A D (moduleFiniteCellOver_representable A D x hx)

lemma modulePerfectOver_mono {S T : Set D} (h : S ⊆ T) :
    modulePerfectOver A D S ≤ modulePerfectOver A D T :=
  ObjectProperty.monotone_retractClosure
    (ObjectProperty.map_monotone (fun _ hM => moduleFiniteCellOver_mono A D h hM)
      (moduleToDerived A D))

lemma modulePerfectOver_of_retract {S : Set D} {X Y : DerivedModuleCategory A D}
    (r : Retract X Y) (hY : modulePerfectOver A D S Y) : modulePerfectOver A D S X :=
  (modulePerfectOver A D S).prop_of_retract r hY

lemma modulePerfectOver_of_iso {S : Set D} {X Y : DerivedModuleCategory A D}
    (e : X ≅ Y) (hX : modulePerfectOver A D S X) : modulePerfectOver A D S Y :=
  (modulePerfectOver A D S).prop_of_iso e hX

/-- perfect対象の生成元への依存も有限集合に制限できる。 -/
lemma modulePerfectOver_iff_finite_generators (S : Set D) (X : DerivedModuleCategory A D) :
    modulePerfectOver A D S X ↔ ∃ t : Finset D, (↑t : Set D) ⊆ S ∧
      modulePerfectOver A D (↑t : Set D) X := by
  constructor
  · intro hX
    obtain ⟨M, hM, hr⟩ := (modulePerfectOver_iff A D S X).1 hX
    obtain ⟨t, ht, hMt⟩ := (moduleFiniteCellOver_iff_finite_generators A D S M).1 hM
    exact ⟨t, ht, (modulePerfectOver_iff A D (↑t : Set D) X).2 ⟨M, hMt, hr⟩⟩
  · rintro ⟨t, ht, hX⟩
    exact modulePerfectOver_mono A D ht X hX

lemma modulePerfect_iff (X : DerivedModuleCategory A D) :
    modulePerfect A D X ↔ ∃ M : ModuleCategory A D,
      moduleFiniteCell A D M ∧ Nonempty (Retract X ((moduleToDerived A D).obj M)) :=
  modulePerfectOver_iff A D Set.univ X

lemma modulePerfect_iff_finite_generators (X : DerivedModuleCategory A D) :
    modulePerfect A D X ↔ ∃ t : Finset D, modulePerfectOver A D (↑t : Set D) X := by
  constructor
  · intro hX
    obtain ⟨t, _, ht⟩ := (modulePerfectOver_iff_finite_generators A D Set.univ X).1 hX
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    exact modulePerfectOver_mono A D (Set.subset_univ _) X ht

instance modulePerfectOverNonempty (S : Set D) : (modulePerfectOver A D S).Nonempty :=
  ObjectProperty.nonempty_of_prop
    (modulePerfectOver_of_finiteCell A D (moduleFiniteCellOver_zero A D S))

instance modulePerfectOverContainsZero (S : Set D) : (modulePerfectOver A D S).ContainsZero :=
  inferInstance

lemma modulePerfectOver_zero (S : Set D) : modulePerfectOver A D S 0 :=
  (modulePerfectOver A D S).prop_zero

instance modulePerfectStableUnderRetracts : (modulePerfect A D).IsStableUnderRetracts :=
  modulePerfectOverStableUnderRetracts A D Set.univ

/-- retract閉な性質への包含は、finite cellの像について確認すれば十分。 -/
lemma modulePerfectOver_le_iff (S : Set D) (P : ObjectProperty (DerivedModuleCategory A D))
    [P.IsStableUnderRetracts] :
    modulePerfectOver A D S ≤ P ↔ ∀ M : ModuleCategory A D,
      moduleFiniteCellOver A D S M → P ((moduleToDerived A D).obj M) := by
  constructor
  · intro h M hM
    exact h _ (modulePerfectOver_of_finiteCell A D hM)
  · intro h X hX
    obtain ⟨M, hM, ⟨r⟩⟩ := (modulePerfectOver_iff A D S X).1 hX
    exact P.prop_of_retract r (h M hM)

end SerrePositivity.DifferentialGraded
