module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Pentagon

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.ObjectProperty.ClosureShift
public import SerrePositivity.CategoryTheory.Karoubi.Basic
public import SerrePositivity.CategoryTheory.Karoubi.Triangulated
public import SerrePositivity.DifferentialGraded.Derived.Projective

public import Mathlib.CategoryTheory.Triangulated.Subcategory

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import SerrePositivity.DifferentialGraded.Derived.Functor
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import SerrePositivity.HomologicalAlgebra.Complex.StrictlyPerfect
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import SerrePositivity.DifferentialGraded.Module.FreeSphere
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Shift.CommShift
public import SerrePositivity.DifferentialGraded.Category.Tensor

/-!
# Perfect.Basic

## 概要
13 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## FiniteCellProjective（旧 SerrePositivity/DifferentialGraded/Perfect/FiniteCellProjective.lean） -/

/-! # 有限cellの全Hom射影性 -/

@[expose] public section FiniteCellProjective
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 有限操作の構成木から、全Hom endによる射影性を帰納的に得る。 -/
lemma ModuleFiniteCellCode.homotopicallyProjective {S : Set D} {M : ModuleCategory A D}
    (c : ModuleFiniteCellCode A D S M) : moduleHomotopicallyProjective A D M := by
  induction c with
  | zero => exact moduleHomotopicallyProjective_of_isZero A D (moduleZero_isZero A D)
  | generator x hx => exact representable_homotopicallyProjective A D x
  | shift s c ih => exact moduleHomotopicallyProjective_shift A D ih s
  | sum c d ihc ihd => exact moduleHomotopicallyProjective_biprod A D ihc ihd
  | cone c d f ihc ihd => exact moduleHomotopicallyProjective_cone A D ihc ihd f
  | iso c e ih => exact moduleHomotopicallyProjective_of_iso A D e ih

lemma moduleFiniteCellOver_homotopicallyProjective {S : Set D} {M : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) : moduleHomotopicallyProjective A D M := by
  obtain ⟨c⟩ := hM
  exact c.homotopicallyProjective A D

lemma moduleFiniteCell_homotopicallyProjective {M : ModuleCategory A D}
    (hM : moduleFiniteCell A D M) : moduleHomotopicallyProjective A D M :=
  moduleFiniteCellOver_homotopicallyProjective A D hM

/-- finite cellはHom_DのA-flat性なしに相対K-flatでもある。 -/
lemma moduleFiniteCell_relativeKFlat {M : ModuleCategory A D}
    (hM : moduleFiniteCell A D M) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M) :=
  moduleHomotopicallyProjective_relativeKFlat A D (moduleFiniteCell_homotopicallyProjective A D hM)

end SerrePositivity.DifferentialGraded
end

end FiniteCellProjective

/-! ## Basic（旧 SerrePositivity/DifferentialGraded/Perfect/Basic.lean） -/

/-! # 指定導来圏内のfinite cellのretractとしてのPerf -/

@[expose] public section Basic
universe u v

noncomputable section
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
end

end Basic

/-! ## Shift（旧 SerrePositivity/DifferentialGraded/Perfect/Shift.lean） -/

/-! # finite cellとPerfの整数shift閉性 -/

@[expose] public section Shift
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleFiniteCellOverStableUnderShift (S : Set D) :
    (moduleFiniteCellOver A D S).IsStableUnderShift ℤ where
  isStableUnderShiftBy s := ⟨fun _ hM => moduleFiniteCellOver_shift A D hM s⟩

instance derivedFiniteCellOverStableUnderShift (S : Set D) :
    (derivedFiniteCellOver A D S).IsStableUnderShift ℤ where
  isStableUnderShiftBy s := ⟨by
    rintro X ⟨M, hM, ⟨e⟩⟩
    exact ⟨M⟦s⟧, moduleFiniteCellOver_shift A D hM s,
      ⟨((moduleToDerived A D).commShiftIso s).app M ≪≫
        (shiftFunctor (DerivedModuleCategory A D) s).mapIso e⟩⟩⟩

instance modulePerfectOverStableUnderShift (S : Set D) :
    (modulePerfectOver A D S).IsStableUnderShift ℤ := by
  dsimp [modulePerfectOver]
  infer_instance

lemma modulePerfectOver_shift {S : Set D} {X : DerivedModuleCategory A D}
    (hX : modulePerfectOver A D S X) (s : ℤ) : modulePerfectOver A D S (X⟦s⟧) :=
  (modulePerfectOver A D S).le_shift s X hX

lemma modulePerfect_shift {X : DerivedModuleCategory A D}
    (hX : modulePerfect A D X) (s : ℤ) : modulePerfect A D (X⟦s⟧) :=
  modulePerfectOver_shift A D hX s

/-- 既存の充満部分圏shiftを使う包含関手はzero/add coherenceを保つ。 -/
instance perfectModuleInclusionCommShift (S : Set D) :
    (perfectModuleInclusion A D S).CommShift ℤ := by
  dsimp [perfectModuleInclusion]
  infer_instance

instance modulePerfectStableUnderShift : (modulePerfect A D).IsStableUnderShift ℤ :=
  modulePerfectOverStableUnderShift A D Set.univ

end SerrePositivity.DifferentialGraded
end

end Shift

/-! ## KaroubiCriterion（旧 SerrePositivity/DifferentialGraded/Perfect/KaroubiCriterion.lean） -/

/-! # Perfとfinite cell部分圏のKaroubi延長の本質像 -/

@[expose] public section KaroubiCriterion
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Idempotents
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定導来圏内のfinite cellの本質的像の充満部分圏。 -/
abbrev DerivedFiniteCellCategoryOver (S : Set D) := (derivedFiniteCellOver A D S).FullSubcategory

def derivedFiniteCellInclusion (S : Set D) :
    DerivedFiniteCellCategoryOver A D S ⥤ DerivedModuleCategory A D :=
  (derivedFiniteCellOver A D S).ι

instance derivedFiniteCellInclusionFull (S : Set D) :
    (derivedFiniteCellInclusion A D S).Full := by
  dsimp [derivedFiniteCellInclusion]
  infer_instance

instance derivedFiniteCellInclusionFaithful (S : Set D) :
    (derivedFiniteCellInclusion A D S).Faithful := by
  dsimp [derivedFiniteCellInclusion]
  infer_instance

instance derivedFiniteCellInclusionCommShift (S : Set D) :
    (derivedFiniteCellInclusion A D S).CommShift ℤ := by
  dsimp [derivedFiniteCellInclusion]
  infer_instance

/-- 既存一般APIで構成する、finite cell包含のKaroubi延長。 -/
def finiteCellKaroubiFunctor (S : Set D) :
    Karoubi (DerivedFiniteCellCategoryOver A D S) ⥤ Karoubi (DerivedModuleCategory A D) :=
  (functorExtension₂ _ _).obj (derivedFiniteCellInclusion A D S)

instance finiteCellKaroubiFunctorFull (S : Set D) : (finiteCellKaroubiFunctor A D S).Full := by
  dsimp [finiteCellKaroubiFunctor]
  infer_instance

instance finiteCellKaroubiFunctorFaithful (S : Set D) :
    (finiteCellKaroubiFunctor A D S).Faithful := by
  dsimp [finiteCellKaroubiFunctor]
  infer_instance

/-- Karoubi延長は元のfinite cell包含と自然同型で可換。 -/
def finiteCellKaroubiFunctor_fac (S : Set D) :
    toKaroubi (DerivedFiniteCellCategoryOver A D S) ⋙ finiteCellKaroubiFunctor A D S ≅
      derivedFiniteCellInclusion A D S ⋙ toKaroubi (DerivedModuleCategory A D) :=
  (functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app (derivedFiniteCellInclusion A D S)

/-- D(D)内のperfect対象は、Karoubi延長の本質像に入る対象と正確に一致する。 -/
lemma modulePerfectOver_iff_karoubi_essImage (S : Set D) (X : DerivedModuleCategory A D) :
    modulePerfectOver A D S X ↔
      (finiteCellKaroubiFunctor A D S).essImage
        ((toKaroubi (DerivedModuleCategory A D)).obj X) := by
  constructor
  · rintro ⟨Y, hY, ⟨r⟩⟩
    exact karoubiExtension_mem_essImage (derivedFiniteCellInclusion A D S)
      ((toKaroubi (DerivedModuleCategory A D)).obj X) ⟨Y, hY⟩
      (r.map (toKaroubi (DerivedModuleCategory A D)))
  · rintro ⟨P, ⟨e⟩⟩
    let rK : Retract ((toKaroubi (DerivedModuleCategory A D)).obj X)
        ((toKaroubi (DerivedModuleCategory A D)).obj P.X.obj) :=
      ((Retract.ofIso e.symm).trans
        ((karoubiRetract P).map (finiteCellKaroubiFunctor A D S))).trans
          (Retract.ofIso ((finiteCellKaroubiFunctor_fac A D S).app P.X))
    let r : Retract X P.X.obj :=
      { i := rK.i.f
        r := rK.r.f
        retract := by
          have h := congrArg Karoubi.Hom.f rK.retract
          exact h }
    exact ObjectProperty.prop_retractClosure P.X.property r

instance finiteCellKaroubiFunctorCommShift (S : Set D) :
    (finiteCellKaroubiFunctor A D S).CommShift ℤ :=
  karoubiExtension_commShift (derivedFiniteCellInclusion A D S)

instance finiteCellKaroubiFunctorFacCommShift (S : Set D) :
    NatTrans.CommShift (finiteCellKaroubiFunctor_fac A D S).hom ℤ :=
  karoubiExtensionFactors_commShift (derivedFiniteCellInclusion A D S)

lemma modulePerfect_iff_karoubi_essImage (X : DerivedModuleCategory A D) :
    modulePerfect A D X ↔ (finiteCellKaroubiFunctor A D Set.univ).essImage
      ((toKaroubi (DerivedModuleCategory A D)).obj X) :=
  modulePerfectOver_iff_karoubi_essImage A D Set.univ X

end SerrePositivity.DifferentialGraded
end

end KaroubiCriterion

/-! ## Triangulated（旧 SerrePositivity/DifferentialGraded/Perfect/Triangulated.lean） -/

/-! # finite cellの導来本質像の三角閉性 -/

@[expose] public section Triangulated
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance derivedFiniteCellOverClosedUnderIso (S : Set D) :
    (derivedFiniteCellOver A D S).IsClosedUnderIsomorphisms := by
  dsimp [derivedFiniteCellOver]
  infer_instance

lemma derivedFiniteCellOver_triangle_obj₃ (S : Set D)
    (T : Triangle (DerivedModuleCategory A D)) (hT : T ∈ distTriang (DerivedModuleCategory A D))
    (h₁ : derivedFiniteCellOver A D S T.obj₁) (h₂ : derivedFiniteCellOver A D S T.obj₂) :
    derivedFiniteCellOver A D S T.obj₃ := by
  obtain ⟨M, hM, ⟨eM⟩⟩ := h₁
  obtain ⟨N, hN, ⟨eN⟩⟩ := h₂
  obtain ⟨f, hf⟩ := moduleProjectiveToDerived_map_surjective A D
    (moduleFiniteCellOver_homotopicallyProjective A D hM) (eM.hom ≫ T.mor₁ ≫ eN.inv)
  have he : Arrow.mk (moduleDerivedConeTriangle A D f).mor₁ ≅ Arrow.mk T.mor₁ :=
    Arrow.isoMk eM eN (by
      change eM.hom ≫ T.mor₁ = (moduleToDerived A D).map f ≫ eN.hom
      rw [hf]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
  obtain ⟨e, _⟩ := exists_iso_of_arrow_iso (moduleDerivedConeTriangle A D f) T
    (moduleDerivedConeTriangle_distinguished A D f) hT he
  exact ⟨moduleCone A D f, moduleFiniteCellOver_cone A D hM hN f,
    ⟨Triangle.π₃.mapIso e⟩⟩

instance derivedFiniteCellOverTriangulatedClosed₃ (S : Set D) :
    (derivedFiniteCellOver A D S).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk' (derivedFiniteCellOver_triangle_obj₃ A D S)

instance derivedFiniteCellOverTriangulatedClosed₂ (S : Set D) :
    (derivedFiniteCellOver A D S).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

instance derivedFiniteCellOverContainsZero (S : Set D) :
    (derivedFiniteCellOver A D S).ContainsZero := by
  have : (moduleToDerived A D).Additive := Functor.additive_of_iso (moduleToHomotopyDerivedIso A D)
  exact ⟨⟨(moduleToDerived A D).obj (moduleZero A D),
    (moduleToDerived A D).map_isZero (moduleZero_isZero A D),
    (moduleFiniteCellOver A D S).prop_map_obj (moduleToDerived A D)
      (moduleFiniteCellOver_zero A D S)⟩⟩

instance derivedFiniteCellOverIsTriangulated (S : Set D) :
    (derivedFiniteCellOver A D S).IsTriangulated := by
  constructor

lemma modulePerfectOver_triangle_obj₂ (S : Set D)
    (T : Triangle (DerivedModuleCategory A D)) (hT : T ∈ distTriang (DerivedModuleCategory A D))
    (h₁ : modulePerfectOver A D S T.obj₁) (h₃ : modulePerfectOver A D S T.obj₃) :
    modulePerfectOver A D S T.obj₂ := by
  let P := derivedFiniteCellOver A D S
  have hp : ObjectProperty.extensionProduct P P ≤ P :=
    ObjectProperty.extensionProduct_le_of_isTriangulatedClosed₂ (le_refl P) (le_refl P)
  have hc : ObjectProperty.extensionProduct P.retractClosure P.retractClosure ≤ P.retractClosure :=
    (ObjectProperty.extensionProduct_retractClosure_retractClosure_le P P).trans
      (ObjectProperty.monotone_retractClosure hp)
  exact hc _ ⟨T.obj₁, T.obj₃, T.mor₁, T.mor₂, T.mor₃, hT, h₁, h₃⟩

instance modulePerfectOverTriangulatedClosed₂ (S : Set D) :
    (modulePerfectOver A D S).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.mk' (modulePerfectOver_triangle_obj₂ A D S)

instance modulePerfectOverIsTriangulated (S : Set D) :
    (modulePerfectOver A D S).IsTriangulated := by
  constructor

instance modulePerfectIsTriangulated : (modulePerfect A D).IsTriangulated :=
  modulePerfectOverIsTriangulated A D Set.univ

instance derivedFiniteCellInclusionIsTriangulated (S : Set D) :
    (derivedFiniteCellInclusion A D S).IsTriangulated := by
  dsimp [derivedFiniteCellInclusion]
  infer_instance

instance perfectModuleInclusionIsTriangulated (S : Set D) :
    (perfectModuleInclusion A D S).IsTriangulated := by
  dsimp [perfectModuleInclusion]
  infer_instance

instance finiteCellKaroubiFunctorIsTriangulated (S : Set D) :
    (finiteCellKaroubiFunctor A D S).IsTriangulated := by
  dsimp [finiteCellKaroubiFunctor]
  infer_instance

end SerrePositivity.DifferentialGraded
end

end Triangulated

/-! ## UniversalProperty（旧 SerrePositivity/DifferentialGraded/Perfect/UniversalProperty.lean） -/

/-! # Perfは指定代表加群を含む最小の厚い部分圏 -/

@[expose] public section UniversalProperty
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : ObjectProperty (DerivedModuleCategory A D)) [P.IsTriangulated]
  [P.IsClosedUnderIsomorphisms]

lemma moduleDerivedBiprod_mem_triangulated {M N : ModuleCategory A D}
    (hM : P ((moduleToDerived A D).obj M)) (hN : P ((moduleToDerived A D).obj N)) :
    P ((moduleToDerived A D).obj (moduleBiprod A D M N)) := by
  have : PreservesBinaryBiproducts (moduleToDerived A D) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have h := P.ext_of_isTriangulatedClosed₂'
    (binaryBiproductTriangle ((moduleToDerived A D).obj M) ((moduleToDerived A D).obj N))
    (binaryBiproductTriangle_distinguished _ _) hM hN
  rw [ObjectProperty.isoClosure_eq_self] at h
  exact P.prop_of_iso
    ((moduleToDerived A D).mapIso (moduleBiprodIso A D M N) ≪≫
      (moduleToDerived A D).mapBiprod M N).symm h

lemma ModuleFiniteCellCode.mem_triangulated {S : Set D}
    (hgen : ∀ x ∈ S, P ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x))))
    {M : ModuleCategory A D} (c : ModuleFiniteCellCode A D S M) :
    P ((moduleToDerived A D).obj M) := by
  induction c with
  | zero => exact P.prop_of_isZero ((moduleToDerived A D).map_isZero (moduleZero_isZero A D))
  | generator x hx => exact hgen x hx
  | @shift M s c ih =>
    exact P.prop_of_iso (((moduleToDerived A D).commShiftIso s).app M).symm
      (P.le_shift s _ ih)
  | sum c d ihc ihd => exact moduleDerivedBiprod_mem_triangulated A D P ihc ihd
  | cone c d f ihc ihd =>
    have h := P.ext_of_isTriangulatedClosed₃' (moduleDerivedConeTriangle A D f)
      (moduleDerivedConeTriangle_distinguished A D f) ihc ihd
    rw [ObjectProperty.isoClosure_eq_self] at h
    exact h
  | iso c e ih => exact P.prop_of_iso ((moduleToDerived A D).mapIso e) ih

lemma derivedFiniteCellOver_le_iff_generators (S : Set D) :
    derivedFiniteCellOver A D S ≤ P ↔ ∀ x ∈ S, P ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x))) := by
  constructor
  · intro h x hx
    exact h _ ((moduleFiniteCellOver A D S).prop_map_obj (moduleToDerived A D)
      (moduleFiniteCellOver_representable A D x hx))
  · intro h X hX
    obtain ⟨M, ⟨c⟩, ⟨e⟩⟩ := hX
    exact P.prop_of_iso e (c.mem_triangulated A D P h)

lemma modulePerfectOver_le_of_generators [P.IsStableUnderRetracts] (S : Set D)
    (hgen : ∀ x ∈ S, P ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x)))) :
    modulePerfectOver A D S ≤ P := by
  rw [modulePerfectOver_le_iff]
  intro M hM
  obtain ⟨c⟩ := hM
  exact c.mem_triangulated A D P hgen

lemma modulePerfectOver_le_iff_generators [P.IsStableUnderRetracts] (S : Set D) :
    modulePerfectOver A D S ≤ P ↔ ∀ x ∈ S, P ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x))) := by
  constructor
  · intro h x hx
    exact h _ (modulePerfectOver_representable A D x hx)
  · exact modulePerfectOver_le_of_generators A D P S

lemma modulePerfect_le_iff_generators [P.IsStableUnderRetracts] :
    modulePerfect A D ≤ P ↔ ∀ x : D, P ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x))) := by
  change modulePerfectOver A D Set.univ ≤ P ↔ _
  rw [modulePerfectOver_le_iff_generators]
  simp only [Set.mem_univ, forall_const]

end SerrePositivity.DifferentialGraded
end

end UniversalProperty

/-! ## KaroubiEquivalence（旧 SerrePositivity/DifferentialGraded/Perfect/KaroubiEquivalence.lean） -/

/-! # finite cellのKaroubi包絡と指定導来圏内のPerfとの三角同値 -/

@[expose] public section KaroubiEquivalence
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleDerivedKaroubiEquivalence :
    DerivedModuleCategory A D ≌ Karoubi (DerivedModuleCategory A D) :=
  toKaroubiEquivalence _

instance moduleDerivedKaroubiEquivalenceFunctorCommShift :
    (moduleDerivedKaroubiEquivalence A D).functor.CommShift ℤ := by
  change (toKaroubi (DerivedModuleCategory A D)).CommShift ℤ
  infer_instance

instance moduleDerivedKaroubiEquivalenceInverseCommShift :
    (moduleDerivedKaroubiEquivalence A D).inverse.CommShift ℤ :=
  (moduleDerivedKaroubiEquivalence A D).commShiftInverse ℤ

instance moduleDerivedKaroubiEquivalenceCommShift :
    (moduleDerivedKaroubiEquivalence A D).CommShift ℤ :=
  (moduleDerivedKaroubiEquivalence A D).commShift_of_functor ℤ

instance moduleDerivedKaroubiEquivalenceIsTriangulated :
    (moduleDerivedKaroubiEquivalence A D).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (by
    change (toKaroubi (DerivedModuleCategory A D)).IsTriangulated
    infer_instance)

/-- 形式的な有限cell直和因子を、主導来圏の実際の対象として実現する。 -/
def finiteCellKaroubiRealization (S : Set D) :
    Karoubi (DerivedFiniteCellCategoryOver A D S) ⥤ DerivedModuleCategory A D :=
  finiteCellKaroubiFunctor A D S ⋙ (moduleDerivedKaroubiEquivalence A D).inverse

instance finiteCellKaroubiRealizationFull (S : Set D) :
    (finiteCellKaroubiRealization A D S).Full := by
  dsimp [finiteCellKaroubiRealization]
  infer_instance

instance finiteCellKaroubiRealizationFaithful (S : Set D) :
    (finiteCellKaroubiRealization A D S).Faithful := by
  dsimp [finiteCellKaroubiRealization]
  infer_instance

instance finiteCellKaroubiRealizationCommShift (S : Set D) :
    (finiteCellKaroubiRealization A D S).CommShift ℤ := by
  dsimp [finiteCellKaroubiRealization]
  infer_instance

instance finiteCellKaroubiRealizationIsTriangulated (S : Set D) :
    (finiteCellKaroubiRealization A D S).IsTriangulated := by
  dsimp [finiteCellKaroubiRealization]
  infer_instance

def finiteCellKaroubiRealizationToKaroubiIso (S : Set D) :
    finiteCellKaroubiRealization A D S ⋙ toKaroubi (DerivedModuleCategory A D) ≅
      finiteCellKaroubiFunctor A D S :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (finiteCellKaroubiFunctor A D S)
      (moduleDerivedKaroubiEquivalence A D).counitIso ≪≫ Functor.rightUnitor _

instance finiteCellKaroubiRealizationToKaroubiIsoCommShift (S : Set D) :
    NatTrans.CommShift (finiteCellKaroubiRealizationToKaroubiIso A D S).hom ℤ := by
  dsimp [finiteCellKaroubiRealizationToKaroubiIso]
  infer_instance

/-- 実現は、元のfinite cell上では既存の導来圏への包含に一致する。 -/
def finiteCellKaroubiRealization_fac (S : Set D) :
    toKaroubi (DerivedFiniteCellCategoryOver A D S) ⋙ finiteCellKaroubiRealization A D S ≅
      derivedFiniteCellInclusion A D S :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (finiteCellKaroubiFunctor_fac A D S)
      (moduleDerivedKaroubiEquivalence A D).inverse ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (derivedFiniteCellInclusion A D S)
      (moduleDerivedKaroubiEquivalence A D).unitIso.symm ≪≫ Functor.rightUnitor _

instance finiteCellKaroubiRealizationFacCommShift (S : Set D) :
    NatTrans.CommShift (finiteCellKaroubiRealization_fac A D S).hom ℤ := by
  dsimp [finiteCellKaroubiRealization_fac]
  infer_instance

lemma finiteCellKaroubiRealization_perfect (S : Set D)
    (P : Karoubi (DerivedFiniteCellCategoryOver A D S)) :
    modulePerfectOver A D S ((finiteCellKaroubiRealization A D S).obj P) := by
  rw [modulePerfectOver_iff_karoubi_essImage]
  exact ⟨P, ⟨((finiteCellKaroubiRealizationToKaroubiIso A D S).app P).symm⟩⟩

def finiteCellKaroubiToPerfect (S : Set D) :
    Karoubi (DerivedFiniteCellCategoryOver A D S) ⥤ PerfectModuleCategoryOver A D S :=
  (modulePerfectOver A D S).lift (finiteCellKaroubiRealization A D S)
    (finiteCellKaroubiRealization_perfect A D S)

instance finiteCellKaroubiToPerfectFull (S : Set D) :
    (finiteCellKaroubiToPerfect A D S).Full := by
  dsimp [finiteCellKaroubiToPerfect]
  infer_instance

instance finiteCellKaroubiToPerfectFaithful (S : Set D) :
    (finiteCellKaroubiToPerfect A D S).Faithful := by
  dsimp [finiteCellKaroubiToPerfect]
  infer_instance

instance finiteCellKaroubiToPerfectEssSurj (S : Set D) :
    (finiteCellKaroubiToPerfect A D S).EssSurj where
  mem_essImage X := by
    obtain ⟨P, ⟨e⟩⟩ := (modulePerfectOver_iff_karoubi_essImage A D S X.obj).mp X.property
    refine ⟨P, ⟨(modulePerfectOver A D S).isoMk ?_⟩⟩
    exact (moduleDerivedKaroubiEquivalence A D).inverse.mapIso e ≪≫
      ((moduleDerivedKaroubiEquivalence A D).unitIso.app X.obj).symm

instance finiteCellKaroubiToPerfectIsEquivalence (S : Set D) :
    (finiteCellKaroubiToPerfect A D S).IsEquivalence where

instance finiteCellKaroubiToPerfectCommShift (S : Set D) :
    (finiteCellKaroubiToPerfect A D S).CommShift ℤ := by
  dsimp [finiteCellKaroubiToPerfect]
  infer_instance

instance finiteCellKaroubiToPerfectIsTriangulated (S : Set D) :
    (finiteCellKaroubiToPerfect A D S).IsTriangulated := by
  dsimp [finiteCellKaroubiToPerfect]
  infer_instance

def finiteCellKaroubiToPerfectCompInclusion (S : Set D) :
    finiteCellKaroubiToPerfect A D S ⋙ perfectModuleInclusion A D S ≅
      finiteCellKaroubiRealization A D S :=
  (modulePerfectOver A D S).liftCompιIso _ _

instance finiteCellKaroubiToPerfectCompInclusionCommShift (S : Set D) :
    NatTrans.CommShift (finiteCellKaroubiToPerfectCompInclusion A D S).hom ℤ := by
  dsimp [finiteCellKaroubiToPerfectCompInclusion]
  infer_instance

/-- 実際の導来対象としてのPerfとfinite cellのKaroubi包絡との同値。 -/
def finiteCellKaroubiPerfectEquivalence (S : Set D) :
    Karoubi (DerivedFiniteCellCategoryOver A D S) ≌ PerfectModuleCategoryOver A D S :=
  (finiteCellKaroubiToPerfect A D S).asEquivalence

instance finiteCellKaroubiPerfectEquivalenceFunctorCommShift (S : Set D) :
    (finiteCellKaroubiPerfectEquivalence A D S).functor.CommShift ℤ := by
  change (finiteCellKaroubiToPerfect A D S).CommShift ℤ
  infer_instance

instance finiteCellKaroubiPerfectEquivalenceInverseCommShift (S : Set D) :
    (finiteCellKaroubiPerfectEquivalence A D S).inverse.CommShift ℤ :=
  (finiteCellKaroubiPerfectEquivalence A D S).commShiftInverse ℤ

instance finiteCellKaroubiPerfectEquivalenceCommShift (S : Set D) :
    (finiteCellKaroubiPerfectEquivalence A D S).CommShift ℤ :=
  (finiteCellKaroubiPerfectEquivalence A D S).commShift_of_functor ℤ

instance finiteCellKaroubiPerfectEquivalenceIsTriangulated (S : Set D) :
    (finiteCellKaroubiPerfectEquivalence A D S).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (by
    change (finiteCellKaroubiToPerfect A D S).IsTriangulated
    infer_instance)

instance perfectModuleCategoryOverIsIdempotentComplete (S : Set D) :
    IsIdempotentComplete (PerfectModuleCategoryOver A D S) :=
  Idempotents.Equivalence.isIdempotentComplete
    (finiteCellKaroubiPerfectEquivalence A D S) inferInstance

end SerrePositivity.DifferentialGraded
end

end KaroubiEquivalence

/-! ## FiniteProjectiveImage（旧 SerrePositivity/DifferentialGraded/Perfect/FiniteProjectiveImage.lean） -/

/-! # 有限射影加群の像のperfect性

既存の有限自由加群へのretractを再利用する。有限和は主Perfの充満部分圏で取り、
その包含によるbiproduct比較で主導来圏へ戻す。
-/

@[expose] public section FiniteProjectiveImage
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 指定生成集合の主Perfは有限biproductで閉じる。 -/
lemma modulePerfectOver_biproduct (S : Set D) {J : Type} [Finite J]
    (X : J → DerivedModuleCategory A D) (hX : ∀ j, modulePerfectOver A D S (X j)) :
    modulePerfectOver A D S (⨁ X) := by
  let Y : J → PerfectModuleCategoryOver A D S := fun j => ⟨X j, hX j⟩
  let e : (perfectModuleInclusion A D S).obj (⨁ Y) ≅ ⨁ X :=
    (perfectModuleInclusion A D S).mapBiproduct Y
  exact (modulePerfectOver A D S).prop_of_iso e (⨁ Y).property

/-- 加法的関手がAをperfect対象へ送れば、任意の有限射影A加群もperfect対象へ送る。 -/
lemma modulePerfectOver_image_finiteProjective (S : Set D)
    (F : ModuleCat.{u} A ⥤ DerivedModuleCategory A D) [F.Additive]
    (hA : modulePerfectOver A D S (F.obj (ModuleCat.of A A)))
    (M : ModuleCat.{u} A) [Module.Finite A M] [Module.Projective A M] :
    modulePerfectOver A D S (F.obj M) := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  let r : Retract M (ModuleCat.of A (Fin n → A)) :=
    ⟨ModuleCat.ofHom g, ModuleCat.ofHom f, ModuleCat.hom_ext hfg⟩
  let X : Fin n → ModuleCat.{u} A := fun _ => ModuleCat.of A A
  let e : F.obj (ModuleCat.of A (Fin n → A)) ≅ ⨁ (fun j => F.obj (X j)) :=
    F.mapIso (ModuleCat.biproductIsoPi X).symm ≪≫ F.mapBiproduct X
  have hfree := (modulePerfectOver A D S).prop_of_iso e.symm
    (modulePerfectOver_biproduct A D S (fun j => F.obj (X j)) (fun _ => hA))
  exact modulePerfectOver_of_retract A D (r.map F) hfree

end SerrePositivity.DifferentialGraded
end

end FiniteProjectiveImage

/-! ## RingSingle（旧 SerrePositivity/DifferentialGraded/Perfect/RingSingle.lean） -/

/-! # 次数0に集中する有限射影複体の主導来像はperfect -/

@[expose] public section RingSingle
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex MonoidalCategory
variable (A : Type u) [CommRing A]

/-- 一対象Aの代表加群は単位複体の定数加群と厳密に一致する。 -/
lemma ringModule_unit_eq_representable :
    ringModule A (𝟙_ (Complex A)) = representable A (D := PUnit.{1}) PUnit.unit :=
  ringModule_recover A (representable A (D := PUnit.{1}) PUnit.unit)

/-- 次数0の通常加群を主dg加群導来圏へ送る加法的関手。 -/
def ringSingleZeroToDerived : ModuleCat.{u} A ⥤ DerivedModuleCategory A PUnit.{1} :=
  single (ModuleCat.{u} A) (.up ℤ) 0 ⋙ complexToRingModule A ⋙ moduleToDerived A PUnit.{1}

instance ringSingleZeroToDerivedAdditive : (ringSingleZeroToDerived A).Additive := by
  dsimp [ringSingleZeroToDerived]
  infer_instance

/-- 基礎環Aの次数0像は主Perfの代表生成元である。 -/
lemma ringSingleZeroToDerived_unit_perfect :
    modulePerfect A PUnit.{1} ((ringSingleZeroToDerived A).obj (ModuleCat.of A A)) := by
  change modulePerfect A PUnit.{1} ((moduleToDerived A PUnit.{1}).obj
    (ForgetEnrichment.of (Complex A) (ringModule A (𝟙_ (Complex A)))))
  rw [ringModule_unit_eq_representable]
  exact modulePerfectOver_representable A PUnit.{1} PUnit.unit (Set.mem_univ _)

/-- 有限射影加群の次数0像は、有限個の代表生成元の和のretractとしてperfect。 -/
lemma ringSingleZeroToDerived_finiteProjective_perfect (M : ModuleCat.{u} A)
    [Module.Finite A M] [Module.Projective A M] :
    modulePerfect A PUnit.{1} ((ringSingleZeroToDerived A).obj M) :=
  modulePerfectOver_image_finiteProjective A PUnit.{1} Set.univ (ringSingleZeroToDerived A)
    (ringSingleZeroToDerived_unit_perfect A) M

end SerrePositivity.DifferentialGraded
end

end RingSingle

/-! ## RingSingleShift（旧 SerrePositivity/DifferentialGraded/Perfect/RingSingleShift.lean） -/

/-! # 全整数次数に集中する有限射影複体のperfect性 -/

@[expose] public section RingSingleShift
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex MonoidalCategory
variable (A : Type u) [CommRing A]

/-- 一対象加群の厳密な復元を使い、実際のshift対象を照合する。 -/
lemma ringModule_shift_eq (P : Complex A) (s : ℤ) :
    ringModule A (P⟦s⟧) = shiftModule s (ringModule A P) :=
  ringModule_recover A (shiftModule s (ringModule A P))

/-- 通常複体から主加群への比較はshift対象に関して厳密な同型を持つ。 -/
def complexToRingModuleShiftObjIso (P : Complex A) (s : ℤ) :
    (complexToRingModule A).obj (P⟦s⟧) ≅ ((complexToRingModule A).obj P)⟦s⟧ :=
  eqToIso (congrArg (ForgetEnrichment.of (Complex A)) (ringModule_shift_eq A P s))

/-- 次数nの通常加群を主dg加群導来圏へ送る。 -/
def ringSingleToDerived (n : ℤ) : ModuleCat.{u} A ⥤ DerivedModuleCategory A PUnit.{1} :=
  single (ModuleCat.{u} A) (.up ℤ) n ⋙ complexToRingModule A ⋙ moduleToDerived A PUnit.{1}

instance ringSingleToDerivedAdditive (n : ℤ) : (ringSingleToDerived A n).Additive := by
  dsimp [ringSingleToDerived]
  infer_instance

/-- sphere nの主導来像は、代表生成元の−n shiftと同型なのでperfect。 -/
lemma ringSingleToDerived_unit_perfect (n : ℤ) :
    modulePerfect A PUnit.{1} ((ringSingleToDerived A n).obj (ModuleCat.of A A)) := by
  let F := complexToRingModule A
  let Q := moduleToDerived A PUnit.{1}
  let e : (complexSphere A 0)⟦-n⟧ ≅ complexSphere A n :=
    complexSphereShiftIso A 0 (-n) ≪≫ eqToIso (by congr 1; omega)
  let eM : (F.obj (complexSphere A 0))⟦-n⟧ ≅ F.obj (complexSphere A n) :=
    (complexToRingModuleShiftObjIso A (complexSphere A 0) (-n)).symm ≪≫ F.mapIso e
  let eD : (Q.obj (F.obj (complexSphere A 0)))⟦-n⟧ ≅ Q.obj (F.obj (complexSphere A n)) :=
    ((Q.commShiftIso (-n)).app _).symm ≪≫ Q.mapIso eM
  exact (modulePerfect A PUnit.{1}).prop_of_iso eD
    (modulePerfect_shift A PUnit.{1} (ringSingleZeroToDerived_unit_perfect A) (-n))

/-- 任意整数次数の有限射影加群の主導来像はperfect。 -/
lemma ringSingleToDerived_finiteProjective_perfect (n : ℤ) (M : ModuleCat.{u} A)
    [Module.Finite A M] [Module.Projective A M] :
    modulePerfect A PUnit.{1} ((ringSingleToDerived A n).obj M) :=
  modulePerfectOver_image_finiteProjective A PUnit.{1} Set.univ (ringSingleToDerived A n)
    (ringSingleToDerived_unit_perfect A n) M

end SerrePositivity.DifferentialGraded
end

end RingSingleShift

/-! ## RingExtensions（旧 SerrePositivity/DifferentialGraded/Perfect/RingExtensions.lean） -/

/-! # 通常複体の短完全列による主導来perfect性の拡張

既存の一対象導来同値で通常の短完全列の三角形を主導来圏へ戻す。
-/

@[expose] public section RingExtensions
universe u w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex MonoidalCategory Pretriangulated
variable (A : Type u) [CommRing A]

/-- 実際のdg関手の合成比較から、通常複体の評価比較を得る。 -/
def complexToRingModuleEvaluationIso :
    complexToRingModule A ⋙ moduleEvaluation A PUnit.{1} PUnit.unit ≅ 𝟭 (Complex A) := by
  let I := ForgetEnrichment.equivInverse (Complex A) (Complex A)
  let C := (ringConstantDG A).onClosed
  let V := (moduleEvaluationDG A PUnit.{1} PUnit.unit).onClosed
  let E := closedToComplex A
  let h : C ⋙ V ≅ 𝟭 (ClosedCategory A (Complex A)) :=
    (EnrichedFunctor.forgetComp (ringConstantDG A)
      (moduleEvaluationDG A PUnit.{1} PUnit.unit)).symm ≪≫
    eqToIso (congrArg (fun F => DGFunctor.onClosed F) (ringConstantDG_comp_evaluation A)) ≪≫
    EnrichedFunctor.forgetId (Complex A) (Complex A)
  exact Functor.associator I C (V ⋙ E) ≪≫
    Functor.isoWhiskerLeft I ((Functor.associator C V E).symm ≪≫
      Functor.isoWhiskerRight h E ≪≫ Functor.leftUnitor E) ≪≫
    (ForgetEnrichment.equiv (Complex A) (D := Complex A)).counitIso

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 主導来像を一対象導来同値で評価すると既存Qと自然同型で一致する。 -/
def complexToRingModuleDerivedEvaluationIso :
    (complexToRingModule A ⋙ moduleToDerived A PUnit.{1}) ⋙
      (ringDerivedEquivalence A).functor ≅ DerivedCategory.Q (C := ModuleCat.{u} A) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (complexToRingModule A) (ringDerivedEquivalence_fac A) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (complexToRingModuleEvaluationIso A) DerivedCategory.Q ≪≫
    Functor.leftUnitor _

/-- 既存導来圏の通常複体の像を同値の逆で戻すと、実際の主dg加群の像と一致する。 -/
def ringComplexDerivedUnitIso (P : Complex A) :
    (ringDerivedEquivalence A).inverse.obj (DerivedCategory.Q.obj P) ≅
      (moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj P) :=
  (ringDerivedEquivalence A).inverse.mapIso
      ((complexToRingModuleDerivedEvaluationIso A).app P).symm ≪≫
    ((ringDerivedEquivalence A).unitIso.app _).symm

/-- 通常複体の短完全列の両端の主導来像がperfectなら中央もperfect。 -/
lemma ringComplexDerived_perfect_of_shortExact (S : ShortComplex (Complex A))
    (hS : S.ShortExact)
    (h₁ : modulePerfect A PUnit.{1}
      ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj S.X₁)))
    (h₃ : modulePerfect A PUnit.{1}
      ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj S.X₃))) :
    modulePerfect A PUnit.{1}
      ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj S.X₂)) := by
  let E := ringDerivedEquivalence A
  let T := E.inverse.mapTriangle.obj (DerivedCategory.triangleOfSES hS)
  have hT : T ∈ distTriang (DerivedModuleCategory A PUnit.{1}) :=
    E.inverse.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS)
  exact (modulePerfect A PUnit.{1}).prop_of_iso (ringComplexDerivedUnitIso A S.X₂)
    (modulePerfectOver_triangle_obj₂ A PUnit.{1} Set.univ T hT
      ((modulePerfect A PUnit.{1}).prop_of_iso (ringComplexDerivedUnitIso A S.X₁).symm h₁)
      ((modulePerfect A PUnit.{1}).prop_of_iso (ringComplexDerivedUnitIso A S.X₃).symm h₃))

end SerrePositivity.DifferentialGraded
end

end RingExtensions

/-! ## RingShiftComparison（旧 SerrePositivity/DifferentialGraded/Perfect/RingShiftComparison.lean） -/

/-! # 一対象Aの通常複体比較と導来比較の整合的shift

既存の実際の評価との自然同型を、完全忠実な評価に沿って持ち上げる。
shiftの零・和coherenceと比較自然変換の整合性を同時に得る。
-/

@[expose] public section RingShiftComparison
universe u w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 通常複体から一対象dg加群への比較のshiftは、実際の評価を通じて一意に整合する。 -/
instance complexToRingModuleCommShift : (complexToRingModule A).CommShift ℤ :=
  Functor.CommShift.ofComp (complexToRingModuleEvaluationIso A) ℤ

/-- 評価との恒等比較は零・加法coherenceを持つshiftに整合する。 -/
instance complexToRingModuleEvaluationIsoCommShift :
    NatTrans.CommShift (complexToRingModuleEvaluationIso A).hom ℤ :=
  Functor.CommShift.ofComp_compatibility (complexToRingModuleEvaluationIso A) ℤ

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 主導来評価と既存Qとの比較も整数shiftに整合する。 -/
instance complexToRingModuleDerivedEvaluationIsoCommShift :
    NatTrans.CommShift (complexToRingModuleDerivedEvaluationIso A).hom ℤ := by
  have : NatTrans.CommShift (Functor.isoWhiskerLeft (complexToRingModule A)
      (ringDerivedEquivalence_fac A)).hom ℤ := by
    change NatTrans.CommShift (Functor.whiskerLeft _ (ringDerivedEquivalence_fac A).hom) ℤ
    infer_instance
  have : NatTrans.CommShift (Functor.isoWhiskerRight
      (complexToRingModuleEvaluationIso A) (DerivedCategory.Q (C := ModuleCat.{u} A))).hom ℤ := by
    change NatTrans.CommShift (Functor.whiskerRight (complexToRingModuleEvaluationIso A).hom _) ℤ
    infer_instance
  dsimp only [complexToRingModuleDerivedEvaluationIso, Iso.trans_hom, Iso.symm_hom]
  apply NatTrans.CommShift.comp

/-- 既存一対象導来同値の順逆のshiftはunit/counitとも整合する。 -/
instance ringDerivedEquivalenceShiftCompatible : (ringDerivedEquivalence A).CommShift ℤ :=
  Equivalence.CommShift.mk'' _ _ (ringDerivedEquivalenceCounitCommShift A)

/-- 既存導来圏から一対象同値の逆で戻す比較を、全複体に自然な同型として公開する。 -/
def ringComplexDerivedUnitNatIso :
    DerivedCategory.Q (C := ModuleCat.{u} A) ⋙ (ringDerivedEquivalence A).inverse ≅
      complexToRingModule A ⋙ moduleToDerived A PUnit.{1} :=
  Functor.isoWhiskerRight (complexToRingModuleDerivedEvaluationIso A).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (complexToRingModule A ⋙ moduleToDerived A PUnit.{1})
      (ringDerivedEquivalence A).unitIso.symm ≪≫
    Functor.rightUnitor _

/-- 逆比較自然同型も、既存の導来同値のshiftと整合する。 -/
instance ringComplexDerivedUnitNatIsoCommShift :
    NatTrans.CommShift (ringComplexDerivedUnitNatIso A).hom ℤ := by
  have : NatTrans.CommShift (Functor.isoWhiskerRight
      (complexToRingModuleDerivedEvaluationIso A).symm
      (ringDerivedEquivalence A).inverse).hom ℤ := by
    change NatTrans.CommShift (Functor.whiskerRight
      (complexToRingModuleDerivedEvaluationIso A).inv (ringDerivedEquivalence A).inverse) ℤ
    infer_instance
  have : NatTrans.CommShift (Functor.isoWhiskerLeft
      (complexToRingModule A ⋙ moduleToDerived A PUnit.{1})
      (ringDerivedEquivalence A).unitIso.symm).hom ℤ := by
    change NatTrans.CommShift (Functor.whiskerLeft _ (ringDerivedEquivalence A).unitIso.inv) ℤ
    infer_instance
  dsimp only [ringComplexDerivedUnitNatIso, Iso.trans_hom, Iso.symm_hom]
  apply NatTrans.CommShift.comp

end SerrePositivity.DifferentialGraded
end

end RingShiftComparison

/-! ## RingHomotopyDerivedComparison（旧 SerrePositivity/DifferentialGraded/Perfect/RingHomotopyDerivedComparison.lean） -/

/-! # 実際のdg複体H⁰からの主導来比較と既存Qhの自然同型

閉零圏上の比較を境界商へ降ろす。ホモトピー圏の対象選択を比較の仮定にしない。
-/

@[expose] public section RingHomotopyDerivedComparison
universe u w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 通常複体への閉零比較を戻して定数dg加群へ送ると、元の閉零dg関手と一致する。 -/
def complexClosedRingModuleIso :
    closedToComplex A ⋙ complexToRingModule A ≅ (ringConstantDG A).onClosed :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ForgetEnrichment.equiv (Complex A)
      (D := Complex A)).unitIso.symm (ringConstantDG A).onClosed ≪≫
    Functor.leftUnitor _

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 主dg関手のH⁰と主局所化の合成は、既存の通常Qhを経由する比較と自然同型。 -/
def complexHomotopyRingDerivedIso :
    (ringConstantDG A).onHomotopy ⋙ moduleHomotopyToDerivedClosed A PUnit.{1} ≅
      complexHomotopyComparison A ⋙ DerivedCategory.Qh ⋙ (ringDerivedEquivalence A).inverse := by
  let q := toHomotopy A (Complex A)
  let C := (ringConstantDG A).onClosed
  let L := moduleHomotopyToDerivedClosed A PUnit.{1}
  let Q := moduleToDerived A PUnit.{1}
  let J := (ringDerivedEquivalence A).inverse
  let E := closedToComplex A
  let α : q ⋙ ((ringConstantDG A).onHomotopy ⋙ L) ≅
      (E ⋙ DerivedCategory.Q) ⋙ J :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso ((ringConstantDG A).onHomotopy_fac)) L ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft C (moduleToHomotopyDerivedIso A PUnit.{1}) ≪≫
    Functor.isoWhiskerRight (complexClosedRingModuleIso A).symm Q ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft E (ringComplexDerivedUnitNatIso A).symm ≪≫
    (Functor.associator _ _ _).symm
  let β : q ⋙ (complexHomotopyComparison A ⋙ DerivedCategory.Qh ⋙ J) ≅
      (E ⋙ DerivedCategory.Q) ⋙ J :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (complexHomotopyComparison_fac A)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft E ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)) J) ≪≫
    (Functor.associator _ _ _).symm
  exact CategoryTheory.Quotient.natIsoLift (boundaryRelation A (Complex A)) (α ≪≫ β.symm)

end SerrePositivity.DifferentialGraded
end

end RingHomotopyDerivedComparison

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.2.4.1" (partial := special) "仮定：可換環上の小さい dg 圏の通常の導来加群圏（Lean が強い：この dg 導来模型の場合）。結論：代表加群から有限セルと retract で生成される perfect 対象を定義し、生成元を含む最小の厚い部分圏として判定する（dg 代数の一対象圏の場合に HA の定義と一致する部分）。一般の環スペクトルの加群模型への比較は含まれない。"] _root_.SerrePositivity.DifferentialGraded.modulePerfect
attribute [cite HA "7.2.4.1" (partial := special) "仮定：可換環上の小さい dg 圏の通常の導来加群圏（Lean が強い：この dg 導来模型の場合）。結論：代表加群から有限セルと retract で生成される perfect 対象を定義し、生成元を含む最小の厚い部分圏として判定する（dg 代数の一対象圏の場合に HA の定義と一致する部分）。一般の環スペクトルの加群模型への比較は含まれない。"] _root_.SerrePositivity.DifferentialGraded.modulePerfect_le_iff_generators
attribute [cite HA "7.2.4.24" (partial := stronger-hyp) "仮定：可換環上の小さい dg 圏の通常の導来加群圏と retract で閉じる三角部分圏（Lean が強い：この通常の dg 導来模型の場合）。結論：代表加群を含むことと全 perfect 対象を含むことを同値にする（有限生成元からの厚い生成の部分に一致）。有限生成射影だけからの安定閉包が retract 閉性を自動で持つという HA の強い主張は含まれない。"] _root_.SerrePositivity.DifferentialGraded.modulePerfect_le_iff_generators
