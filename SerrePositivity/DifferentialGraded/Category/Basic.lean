module

public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Quotient.Preadditive
public import Mathlib.CategoryTheory.Quotient.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Category.Basic

## 概要
16 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## Basic（旧 SerrePositivity/DifferentialGraded/Category/Basic.lean） -/

/-! # Ch(A) 豊穣としての dg 圏

別の dg 圏構造体は導入しない。Z⁰ は Mathlib の ForgetEnrichment をそのまま使う。
-/

@[expose] public section Basic
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory MonoidalPreadditive
variable (A : Type u) [CommRing A]

/-- 主モデルは非有界 Ch(A) による Mathlib の豊穣圏。対象宇宙 v は独立。 -/
@[kerodon 00PA]
abbrev DGCategory (D : Type v) := EnrichedCategory (Complex A) D

variable (D : Type v) [DGCategory A D]

/-- 閉次数零の圏。単位複体から Hom 複体への chain map を射にする。 -/
@[kerodon 00PD]
abbrev ClosedCategory := ForgetEnrichment (Complex A) D

/-- 既存の豊穣構造から Hom 複体を取り出す。 -/
abbrev homObject (x y : D) : Complex A := x ⟶[Complex A] y

/-- 豊穣合成の源は Hom(x,y)⊗Hom(y,z)。通常順とは Koszul 交換が必要。 -/
abbrev forwardComposition (x y z : D) := eComp (Complex A) (ForgetEnrichment.to (Complex A) x)
          (ForgetEnrichment.to (Complex A) y) (ForgetEnrichment.to (Complex A) z)

/-- 豊穣構造の constructor。入力は Hom 複体・閉単位・chain map 合成と三つの圏法則。
既存 EnrichedCategory の constructor に直接渡し、独立した公開構造を持たない。 -/
@[instance_reducible]
def ofHomObjects (H : D → D → Complex A)
    (unit : ∀ x, 𝟙_ (Complex A) ⟶ H x x)
    (comp : ∀ x y z, H x y ⊗ H y z ⟶ H x z)
    (left : ∀ x y, (λ_ (H x y)).inv ≫ unit x ▷ _ ≫ comp x x y = 𝟙 _)
    (right : ∀ x y, (ρ_ (H x y)).inv ≫ _ ◁ unit y ≫ comp x y y = 𝟙 _)
    (assoc : ∀ w x y z, (α_ _ _ _).inv ≫ comp w x y ▷ _ ≫ comp w y z =
      _ ◁ comp x y z ≫ comp w x z) : DGCategory A D where
  Hom := H
  id := unit
  comp := comp
  id_comp := left
  comp_id := right
  assoc := assoc

omit [DGCategory A D] in
/-- constructor と accessor の Hom 成分は定義上往復する。 -/
lemma ofHomObjects_hom (H : D → D → Complex A) (unit comp left right assoc) (x y : D) :
    (ofHomObjects A D H unit comp left right assoc).Hom x y = H x y := rfl

/-- Enriched の accessor から元の豊穣構造を復元する。 -/
lemma ofHomObjects_recover :
    ofHomObjects A D (EnrichedCategory.Hom (V := Complex A))
      (eId (Complex A)) (eComp (Complex A)) (e_id_comp (Complex A))
      (e_comp_id (Complex A)) (e_assoc (Complex A)) =
        (inferInstance : DGCategory A D) := rfl

omit [DGCategory A D] in
/-- 双次数合成を入力する constructor。微分との両立から chain map を構成する。
単位・結合則はその chain map に対する法則として要求する。 -/
@[instance_reducible]
def ofComponents (H : D → D → Complex A)
    (unit : ∀ x, 𝟙_ (Complex A) ⟶ H x x)
    (b : ∀ x y z (i j n : ℤ), i + j = n → ((H x y).X i ⊗ (H y z).X j ⟶ (H x z).X n))
    (db : ∀ x y z i j,
      b x y z i j (i + j) rfl ≫ (H x z).d (i + j) (i + j + 1) =
        ((H x y).d i (i + 1) ▷ (H y z).X j) ≫
          b x y z (i + 1) j (i + j + 1) (by omega) +
        i.negOnePow • (((H x y).X i ◁ (H y z).d j (j + 1)) ≫
          b x y z i (j + 1) (i + j + 1) (by omega)))
    (left : ∀ x y, (λ_ (H x y)).inv ≫ unit x ▷ _ ≫
      tensorLift (b x x y) (db x x y) = 𝟙 _)
    (right : ∀ x y, (ρ_ (H x y)).inv ≫ _ ◁ unit y ≫
      tensorLift (b x y y) (db x y y) = 𝟙 _)
    (assoc : ∀ w x y z, (α_ _ _ _).inv ≫
      tensorLift (b w x y) (db w x y) ▷ _ ≫ tensorLift (b w y z) (db w y z) =
      _ ◁ tensorLift (b x y z) (db x y z) ≫ tensorLift (b w x z) (db w x z)) :
    DGCategory A D :=
  ofHomObjects A D H unit (fun x y z => tensorLift (b x y z) (db x y z)) left right assoc

/-- Z⁰ の各 Hom に単位からの chain map の加法群を使う。 -/
instance closedHomGroup (x y : ClosedCategory A D) : AddCommGroup (x ⟶ y) :=
  inferInstanceAs (AddCommGroup (𝟙_ (Complex A) ⟶ homObject A D x y))

/-- Z⁰ の合成は加法的。 -/
instance closedPreadditive : Preadditive (ClosedCategory A D) where
  homGroup := closedHomGroup A D
  add_comp := by
    intro x y z f g h
    change (λ_ (𝟙_ (Complex A))).inv ≫
      ((ForgetEnrichment.homTo (Complex A) f + ForgetEnrichment.homTo (Complex A) g) ⊗ₘ
        ForgetEnrichment.homTo (Complex A) h) ≫ _ = _
    simp only [add_tensor, Preadditive.comp_add, Preadditive.add_comp]
    rfl
  comp_add := by
    intro x y z f g h
    change (λ_ (𝟙_ (Complex A))).inv ≫
      (ForgetEnrichment.homTo (Complex A) f ⊗ₘ
        (ForgetEnrichment.homTo (Complex A) g + ForgetEnrichment.homTo (Complex A) h)) ≫ _ = _
    simp only [tensor_add, Preadditive.comp_add, Preadditive.add_comp]
    rfl

/-- Z⁰ の各 Hom に chain map の A 加群構造を使う。 -/
instance closedHomModule (x y : ClosedCategory A D) : Module A (x ⟶ y) :=
  inferInstanceAs (Module A (𝟙_ (Complex A) ⟶ homObject A D x y))

/-- Z⁰ の A 線形構造。 -/
instance closedLinear : Linear A (ClosedCategory A D) where
  homModule := closedHomModule A D
  smul_comp := by
    intro x y z a f g
    change (λ_ (𝟙_ (Complex A))).inv ≫
      ((a • ForgetEnrichment.homTo (Complex A) f) ⊗ₘ ForgetEnrichment.homTo (Complex A) g) ≫
      eComp (Complex A) (ForgetEnrichment.to (Complex A) x)
          (ForgetEnrichment.to (Complex A) y) (ForgetEnrichment.to (Complex A) z) =
      a • (((λ_ (𝟙_ (Complex A))).inv ≫
        (ForgetEnrichment.homTo (Complex A) f ⊗ₘ ForgetEnrichment.homTo (Complex A) g)) ≫
          eComp (Complex A) (ForgetEnrichment.to (Complex A) x)
          (ForgetEnrichment.to (Complex A) y) (ForgetEnrichment.to (Complex A) z))
    simp only [tensorHom_def, MonoidalLinear.smul_whiskerRight,
      Linear.smul_comp, Linear.comp_smul]
    simp only [Category.assoc]
  comp_smul := by
    intro x y z f a g
    change (λ_ (𝟙_ (Complex A))).inv ≫
      (ForgetEnrichment.homTo (Complex A) f ⊗ₘ (a • ForgetEnrichment.homTo (Complex A) g)) ≫
      eComp (Complex A) (ForgetEnrichment.to (Complex A) x)
        (ForgetEnrichment.to (Complex A) y) (ForgetEnrichment.to (Complex A) z) =
      a • (((λ_ (𝟙_ (Complex A))).inv ≫
        (ForgetEnrichment.homTo (Complex A) f ⊗ₘ ForgetEnrichment.homTo (Complex A) g)) ≫
          eComp (Complex A) (ForgetEnrichment.to (Complex A) x)
            (ForgetEnrichment.to (Complex A) y) (ForgetEnrichment.to (Complex A) z))
    simp only [tensorHom_def, MonoidalLinear.whiskerLeft_smul,
      Linear.smul_comp, Linear.comp_smul]
    simp only [Category.assoc]
end SerrePositivity.DifferentialGraded
end

end Basic

/-! ## Homotopy（旧 SerrePositivity/DifferentialGraded/Category/Homotopy.lean） -/

/-! # dg 圏の H⁰

Z⁰ の単位からの射のホモトピーで商を取る。
単位は次数零に集中するので、この関係は Hom 複体の −1 境界による関係に一致する。
-/

@[expose] public section Homotopy
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 閉次数零射を結ぶ chain homotopy。境界を同一視する関係。 -/
@[kerodon 00PZ]
def boundaryRelation : HomRel (ClosedCategory A D) :=
  fun _ _ f g => Nonempty (Homotopy (ForgetEnrichment.homTo (Complex A) f)
    (ForgetEnrichment.homTo (Complex A) g))

/-- 境界関係は合成に安定な同値関係。
合成との両立は tensor によるホモトピーの写像から証明する。 -/
@[kerodon 00Q3]
instance boundaryCongruence : Congruence (boundaryRelation A D) where
  equivalence :=
    { refl := fun f => ⟨Homotopy.refl _⟩
      symm := fun ⟨h⟩ => ⟨h.symm⟩
      trans := fun ⟨h⟩ ⟨k⟩ => ⟨h.trans k⟩ }
  comp_left := by
    intro x y z f g g' hh
    obtain ⟨h⟩ := hh
    refine ⟨?_⟩
    exact ((mapBifunctorMapHomotopy₂ (ForgetEnrichment.homTo (Complex A) f) h
      (curriedTensor (ModuleCat A)) (.up ℤ)).compLeft (λ_ _).inv).compRight
      (eComp (Complex A) (ForgetEnrichment.to (Complex A) x)
        (ForgetEnrichment.to (Complex A) y) (ForgetEnrichment.to (Complex A) z))
  comp_right := by
    intro x y z f f' g hh
    obtain ⟨h⟩ := hh
    refine ⟨?_⟩
    exact ((mapBifunctorMapHomotopy₁ h (ForgetEnrichment.homTo (Complex A) g)
      (curriedTensor (ModuleCat A)) (.up ℤ)).compLeft (λ_ _).inv).compRight
      (eComp (Complex A) (ForgetEnrichment.to (Complex A) x)
        (ForgetEnrichment.to (Complex A) y) (ForgetEnrichment.to (Complex A) z))

/-- 境界関係は加法と両立する。 -/
lemma boundary_add {x y : ClosedCategory A D} (f f' g g' : x ⟶ y)
    (hf : boundaryRelation A D f f') (hg : boundaryRelation A D g g') :
    boundaryRelation A D (f + g) (f' + g') :=
  ⟨hf.some.add hg.some⟩

/-- 境界関係は任意の A スカラーと両立する。 -/
lemma boundary_smul (a : A) {x y : ClosedCategory A D} (f g : x ⟶ y)
    (h : boundaryRelation A D f g) : boundaryRelation A D (a • f) (a • g) :=
  ⟨h.some.smul a⟩

/-- H⁰ の対象は D の対象、射は Z⁰ の境界による商。 -/
@[kerodon 00Q4]
abbrev HomotopyCategory := CategoryTheory.Quotient (boundaryRelation A D)

/-- H⁰ の合成は境界商上 well-defined で、加法的。 -/
instance homotopyPreadditive : Preadditive (HomotopyCategory A D) :=
  Quotient.preadditive _ (fun {x y} => boundary_add A D (x := x) (y := y))

/-- Z⁰ から H⁰ への商関手。 -/
abbrev toHomotopy : ClosedCategory A D ⥤ HomotopyCategory A D :=
  Quotient.functor (boundaryRelation A D)

/-- 商関手は加法を保存する。 -/
instance toHomotopyAdditive : (toHomotopy A D).Additive :=
  Quotient.functor_additive _ (fun {x y} => boundary_add A D (x := x) (y := y))

/-- H⁰ は A 線形。商のスカラー作用を Mathlib で構成する。 -/
instance homotopyLinear : Linear A (HomotopyCategory A D) :=
  Quotient.linear A _ (boundary_smul A D)

/-- 商関手は A 線形。 -/
instance toHomotopyLinear : (toHomotopy A D).Linear A :=
  Quotient.linear_functor A (boundaryRelation A D) (boundary_smul A D)

/-- H⁰ での等式は、ちょうど境界関係による等式である。 -/
lemma toHomotopy_map_eq_iff {x y : ClosedCategory A D} (f g : x ⟶ y) :
    (toHomotopy A D).map f = (toHomotopy A D).map g ↔ boundaryRelation A D f g :=
  Quotient.functor_map_eq_iff _ _ _
/-- H⁰ の等式は、元の Hom 複体の −1 境界による差に一致する。 -/
lemma toHomotopy_map_eq_iff_boundary {x y : ClosedCategory A D} (f g : x ⟶ y) :
    (toHomotopy A D).map f = (toHomotopy A D).map g ↔
      ∃ h : (homObject A D x y).X (-1),
        (homObject A D x y).d (-1) 0 h =
          (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val -
            (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) g)).val := by
  rw [toHomotopy_map_eq_iff]
  exact unit_homotopy_boundary _ _ _

/-- Z⁰ の射を閉次数零の元として読む同値。 -/
def closedHomEquiv (x y : ClosedCategory A D) :
    (x ⟶ y) ≃ zeroCycles (homObject A D x y) := unitCycleEquiv _

end SerrePositivity.DifferentialGraded
end

end Homotopy

/-! ## HomotopyHomology（旧 SerrePositivity/DifferentialGraded/Category/HomotopyHomology.lean） -/

/-! # dg圏のH⁰の射と主Hom複体の次数零ホモロジー -/

@[expose] public section HomotopyHomology
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable (x y : ClosedCategory A D)

def homotopyHomFromCycle (c : zeroCycles (homObject A D x y)) :
    (toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y :=
  (toHomotopy A D).map ((closedHomEquiv A D x y).symm c)

lemma homotopyHomFromCycle_surjective : Function.Surjective (homotopyHomFromCycle A D x y) := by
  intro f
  obtain ⟨g, rfl⟩ := (toHomotopy A D).map_surjective f
  exact ⟨closedHomEquiv A D x y g,
    congrArg ((toHomotopy A D).map) ((closedHomEquiv A D x y).symm_apply_apply g)⟩

lemma homotopyHomFromCycle_eq_iff (c d : zeroCycles (homObject A D x y)) :
    homotopyHomFromCycle A D x y c = homotopyHomFromCycle A D x y d ↔
      c - d ∈ LinearMap.range ((homObject A D x y).sc' (-1) 0 1).moduleCatToCycles := by
  rw [homotopyHomFromCycle, homotopyHomFromCycle, toHomotopy_map_eq_iff_boundary]
  change (∃ h, (homObject A D x y).d (-1) 0 h =
    (cycleFromUnit _ (unitFromCycle _ c)).val -
      (cycleFromUnit _ (unitFromCycle _ d)).val) ↔ _
  rw [cycleFromUnit_unitFromCycle, cycleFromUnit_unitFromCycle]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h, Subtype.ext hh⟩
  · rintro ⟨h, hh⟩
    exact ⟨h, congrArg Subtype.val hh⟩

/-- 具体的なcycle/boundary商からH⁰の実際の射への写像。 -/
def homotopyHomFromCohomologyQuotient :
    ((homObject A D x y).sc' (-1) 0 1).moduleCatLeftHomologyData.H →
      ((toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y) :=
  Quotient.lift (homotopyHomFromCycle A D x y) (fun c d h =>
    (homotopyHomFromCycle_eq_iff A D x y c d).2 ((Submodule.quotientRel_def _).mp h))

lemma homotopyHomFromCohomologyQuotient_bijective :
    Function.Bijective (homotopyHomFromCohomologyQuotient A D x y) := by
  constructor
  · intro c d
    induction c using Quotient.inductionOn with | _ c =>
      induction d using Quotient.inductionOn with | _ d =>
        intro h
        exact Quotient.sound ((Submodule.quotientRel_def _).mpr
          ((homotopyHomFromCycle_eq_iff A D x y c d).1 h))
  · intro f
    obtain ⟨c, hc⟩ := homotopyHomFromCycle_surjective A D x y f
    exact ⟨Submodule.Quotient.mk c, hc⟩

/-- cycle/boundary商とMathlibの次数零ホモロジーの標準比較。 -/
def complexZeroHomologyQuotientIso (K : Complex A) :
    (K.sc' (-1) 0 1).moduleCatLeftHomologyData.H ≅ K.homology 0 :=
  (K.sc' (-1) 0 1).moduleCatHomologyIso.symm ≪≫
    (K.homologyIsoSc' (-1) 0 1 (by simp) (by simp)).symm

def complexZeroHomologyClass (K : Complex A) (c : zeroCycles K) : K.homology 0 :=
  (complexZeroHomologyQuotientIso A K).hom (Submodule.Quotient.mk c)

/-- 対象のHom複体の実際のMathlib homologyを用いるH⁰の射計算。 -/
@[kerodon 00Q4]
def homotopyHomologyEquiv :
    ((toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y) ≃
      (homObject A D x y).homology 0 :=
  (Equiv.ofBijective _ (homotopyHomFromCohomologyQuotient_bijective A D x y)).symm.trans
    (complexZeroHomologyQuotientIso A (homObject A D x y)).toLinearEquiv.toEquiv

lemma homotopyHomologyEquiv_cycle (c : zeroCycles (homObject A D x y)) :
    homotopyHomologyEquiv A D x y (homotopyHomFromCycle A D x y c) =
      complexZeroHomologyClass A (homObject A D x y) c := by
  change (complexZeroHomologyQuotientIso A (homObject A D x y)).hom
    ((Equiv.ofBijective _ (homotopyHomFromCohomologyQuotient_bijective A D x y)).symm
      ((Equiv.ofBijective _ (homotopyHomFromCohomologyQuotient_bijective A D x y))
        (Submodule.Quotient.mk c))) = _
  rw [Equiv.symm_apply_apply]
  rfl

lemma homotopyHomologyEquiv_map (f : x ⟶ y) :
    homotopyHomologyEquiv A D x y ((toHomotopy A D).map f) =
      complexZeroHomologyClass A (homObject A D x y) (closedHomEquiv A D x y f) := by
  simpa only [homotopyHomFromCycle, Equiv.symm_apply_apply] using
    homotopyHomologyEquiv_cycle A D x y (closedHomEquiv A D x y f)

end SerrePositivity.DifferentialGraded
end

end HomotopyHomology

/-! ## HomotopyHomologyLinear（旧 SerrePositivity/DifferentialGraded/Category/HomotopyHomologyLinear.lean） -/

/-! # H⁰の射と主Homのホモロジーの線形比較 -/

@[expose] public section HomotopyHomologyLinear
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A]

lemma complexZeroHomologyClass_add (K : Complex A) (c d : zeroCycles K) :
    complexZeroHomologyClass A K (c + d) =
      complexZeroHomologyClass A K c + complexZeroHomologyClass A K d := by
  exact map_add (complexZeroHomologyQuotientIso A K).hom.hom
    (Submodule.Quotient.mk c) (Submodule.Quotient.mk d)

lemma complexZeroHomologyClass_smul (K : Complex A) (a : A) (c : zeroCycles K) :
    complexZeroHomologyClass A K (a • c) = a • complexZeroHomologyClass A K c := by
  exact map_smul (complexZeroHomologyQuotientIso A K).hom.hom a (Submodule.Quotient.mk c)

variable (D : Type v) [DGCategory A D] (x y : ClosedCategory A D)

lemma closedHomEquiv_add (f g : x ⟶ y) :
    closedHomEquiv A D x y (f + g) = closedHomEquiv A D x y f + closedHomEquiv A D x y g := by
  apply Subtype.ext
  rfl

lemma closedHomEquiv_smul (a : A) (f : x ⟶ y) :
    closedHomEquiv A D x y (a • f) = a • closedHomEquiv A D x y f := by
  apply Subtype.ext
  rfl

lemma homotopyHomologyEquiv_add
    (f g : (toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y) :
    homotopyHomologyEquiv A D x y (f + g) =
      homotopyHomologyEquiv A D x y f + homotopyHomologyEquiv A D x y g := by
  obtain ⟨f, rfl⟩ := (toHomotopy A D).map_surjective f
  obtain ⟨g, rfl⟩ := (toHomotopy A D).map_surjective g
  rw [← (toHomotopy A D).map_add, homotopyHomologyEquiv_map,
    homotopyHomologyEquiv_map, homotopyHomologyEquiv_map, closedHomEquiv_add,
    complexZeroHomologyClass_add]

lemma homotopyHomologyEquiv_smul (a : A)
    (f : (toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y) :
    homotopyHomologyEquiv A D x y (a • f) = a • homotopyHomologyEquiv A D x y f := by
  obtain ⟨f, rfl⟩ := (toHomotopy A D).map_surjective f
  rw [← (toHomotopy A D).map_smul, homotopyHomologyEquiv_map,
    homotopyHomologyEquiv_map, closedHomEquiv_smul, complexZeroHomologyClass_smul]

def homotopyHomologyLinearEquiv :
    ((toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y) ≃ₗ[A]
      (homObject A D x y).homology 0 where
  __ := homotopyHomologyEquiv A D x y
  map_add' := homotopyHomologyEquiv_add A D x y
  map_smul' := homotopyHomologyEquiv_smul A D x y

end SerrePositivity.DifferentialGraded
end

end HomotopyHomologyLinear

/-! ## HomotopyHomologyNaturality（旧 SerrePositivity/DifferentialGraded/Category/HomotopyHomologyNaturality.lean） -/

/-! # cycleのホモロジー類の自然性 -/

@[expose] public section HomotopyHomologyNaturality
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A]

def complexZeroCycle (K : Complex A) (c : zeroCycles K) : K.cycles 0 :=
  (K.cyclesIsoSc' (-1) 0 1 (by simp) (by simp)).inv
    ((K.sc' (-1) 0 1).moduleCatCyclesIso.inv c)

lemma complexZeroCycle_iCycles (K : Complex A) (c : zeroCycles K) :
    K.iCycles 0 (complexZeroCycle A K c) = c.val := by
  dsimp only [complexZeroCycle]
  rw [← ModuleCat.comp_apply, cyclesIsoSc'_inv_iCycles,
    ← ModuleCat.comp_apply, ShortComplex.moduleCatCyclesIso_inv_iCycles]
  rfl

lemma complexZeroHomologyClass_eq (K : Complex A) (c : zeroCycles K) :
    complexZeroHomologyClass A K c = K.homologyπ 0 (complexZeroCycle A K c) := by
  have h : (K.sc' (-1) 0 1).moduleCatLeftHomologyData.π ≫
      (complexZeroHomologyQuotientIso A K).hom =
      (K.sc' (-1) 0 1).moduleCatCyclesIso.inv ≫
        (K.cyclesIsoSc' (-1) 0 1 (by simp) (by simp)).inv ≫ K.homologyπ 0 := by
    dsimp only [complexZeroHomologyQuotientIso, Iso.trans_hom, Iso.symm_hom]
    rw [← ShortComplex.moduleCatCyclesIso_inv_π_assoc, π_homologyIsoSc'_inv]
  exact congrArg (fun f => f c) h

def complexMapZeroCycle {K L : Complex A} (f : K ⟶ L) (c : zeroCycles K) : zeroCycles L :=
  ⟨f.f 0 c.val, by
    have h := congrArg (fun g => g c.val) (f.comm 0 1)
    change L.d 0 1 (f.f 0 c.val) = 0
    change L.d 0 1 (f.f 0 c.val) = f.f 1 (K.d 0 1 c.val) at h
    have hc : K.d 0 1 c.val = 0 := c.property
    rw [hc, map_zero] at h
    exact h⟩

lemma complexZeroCycle_map {K L : Complex A} (f : K ⟶ L) (c : zeroCycles K) :
    cyclesMap f 0 (complexZeroCycle A K c) = complexZeroCycle A L (complexMapZeroCycle A f c) := by
  apply (ModuleCat.mono_iff_injective (L.iCycles 0)).1 inferInstance
  rw [← ModuleCat.comp_apply, cyclesMap_i, ModuleCat.comp_apply,
    complexZeroCycle_iCycles, complexZeroCycle_iCycles]
  rfl

lemma complexZeroHomologyClass_naturality {K L : Complex A} (f : K ⟶ L) (c : zeroCycles K) :
    homologyMap f 0 (complexZeroHomologyClass A K c) =
      complexZeroHomologyClass A L (complexMapZeroCycle A f c) := by
  rw [complexZeroHomologyClass_eq, ← ModuleCat.comp_apply, homologyπ_naturality,
    ModuleCat.comp_apply, complexZeroCycle_map, complexZeroHomologyClass_eq]

variable (D : Type v) [DGCategory A D] {x y z : ClosedCategory A D}
open MonoidalCategory

lemma closedHomEquiv_postcompose (f : x ⟶ y) (g : y ⟶ z) :
    complexMapZeroCycle A (eHomWhiskerLeft (Complex A) x g) (closedHomEquiv A D x y f) =
      closedHomEquiv A D x z (f ≫ g) := by
  have h : eHomEquiv (Complex A) f ≫ eHomWhiskerLeft (Complex A) x g =
      eHomEquiv (Complex A) (f ≫ g) := by
    rw [eHomEquiv_comp, eHomWhiskerLeft, ← Category.assoc, rightUnitor_inv_naturality]
    simp only [Category.assoc, tensorHom_def, unitors_inv_equal]
  apply Subtype.ext
  exact congrArg (fun k => (cycleFromUnit _ k).val) h

lemma homotopyHomologyEquiv_postcompose
    (f : (toHomotopy A D).obj x ⟶ (toHomotopy A D).obj y) (g : y ⟶ z) :
    homotopyHomologyEquiv A D x z (f ≫ (toHomotopy A D).map g) =
      homologyMap (eHomWhiskerLeft (Complex A) x g) 0 (homotopyHomologyEquiv A D x y f) := by
  obtain ⟨f, rfl⟩ := (toHomotopy A D).map_surjective f
  rw [← (toHomotopy A D).map_comp, homotopyHomologyEquiv_map, homotopyHomologyEquiv_map,
    complexZeroHomologyClass_naturality, closedHomEquiv_postcompose]

end SerrePositivity.DifferentialGraded
end

end HomotopyHomologyNaturality

/-! ## Examples（旧 SerrePositivity/DifferentialGraded/Category/Examples.lean） -/

/-! # Ch(A) と一対象 A の dg 圏 -/

@[expose] public section Examples
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 非有界 A 複体の dg 圏。Hom は既存 linearHomComplex。
通常の chain map の Category instance は変更しない。 -/
instance complexEnrichment : DGCategory A (Complex A) where
  Hom := homComplex A
  id := identity
  comp := enrichedComposition
  id_comp := identity_comp
  comp_id := comp_identity
  assoc W X Y Z := by
    rw [enrichedComposition_assoc,
      Iso.inv_hom_id_assoc]

/-- 環 A の一対象 dg 圏。Hom は次数零の tensor unit A。 -/
instance ringEnrichment : DGCategory A PUnit where
  Hom _ _ := 𝟙_ (Complex A)
  id _ := 𝟙 _
  comp _ _ _ := (λ_ (𝟙_ (Complex A))).hom
  id_comp _ _ := by simp
  comp_id _ _ := by
    simp only [whiskerLeft_id]
    monoidal_coherence
  assoc _ _ _ _ := by monoidal_coherence

/-- Ch(A) の閉次数零射は通常の chain map に一致する。 -/
def complexClosedHomEquiv (X Y : Complex A) :
    (ForgetEnrichment.of (Complex A) X ⟶ ForgetEnrichment.of (Complex A) Y) ≃ (X ⟶ Y) :=
  (unitCycleEquiv (homComplex A X Y)).trans
    { toFun c := Cocycle.homOf ⟨c.val, c.property⟩
      invFun f := ⟨Cochain.ofHom f, δ_ofHom f⟩
      left_inv c := by
        apply Subtype.ext
        exact Cocycle.cochain_ofHom_homOf_eq_coe ⟨c.val, c.property⟩
      right_inv f := Cocycle.homOf_ofHom_eq_self f }
/-- 閉射の chain map への比較は、その次数零 cycle を返す。 -/
lemma complexClosedHomEquiv_cochain (X Y : Complex A)
    (f : ForgetEnrichment.of (Complex A) X ⟶ ForgetEnrichment.of (Complex A) Y) :
    Cochain.ofHom (complexClosedHomEquiv A X Y f) =
      (cycleFromUnit (homComplex A X Y) f).val :=
  Cocycle.cochain_ofHom_homOf_eq_coe _

/-- Z⁰(Ch(A)) の単位は通常の恒等 chain map に一致する。 -/
lemma complexClosedHomEquiv_id (X : Complex A) :
    complexClosedHomEquiv A X X (𝟙 (ForgetEnrichment.of (Complex A) X)) = 𝟙 X := by
  apply Cochain.ofHom_injective
  rw [complexClosedHomEquiv_cochain]
  change (cycleFromUnit (homComplex A X X) (identity X)).val = _
  rw [identity, cycleFromUnit_unitFromCycle]

/-- Z⁰(Ch(A)) の合成は通常の chain map 合成に一致する。 -/
lemma complexClosedHomEquiv_comp (X Y Z : Complex A)
    (f : ForgetEnrichment.of (Complex A) X ⟶ ForgetEnrichment.of (Complex A) Y)
    (g : ForgetEnrichment.of (Complex A) Y ⟶ ForgetEnrichment.of (Complex A) Z) :
    complexClosedHomEquiv A X Z (f ≫ g) =
      complexClosedHomEquiv A X Y f ≫ complexClosedHomEquiv A Y Z g := by
  apply Cochain.ofHom_injective
  rw [complexClosedHomEquiv_cochain, Cochain.ofHom_comp,
    complexClosedHomEquiv_cochain, complexClosedHomEquiv_cochain]
  change (cycleFromUnit (homComplex A X Z)
    (((λ_ (𝟙_ (Complex A))).inv ≫ (f ⊗ₘ g)) ≫ enrichedComposition X Y Z)).val = _
  rw [cycleFromUnit_postcomp]
  change (enrichedComposition X Y Z).f 0
    ((((λ_ (𝟙_ (Complex A))).inv ≫ (f ⊗ₘ g)).f 0) (1 : A)) = _
  rw [unit_tensor_apply]
  change (enrichedComposition X Y Z).f 0
    (HomologicalComplex.ιTensorObj (homComplex A X Y) (homComplex A Y Z) 0 0 0 rfl
      ((cycleFromUnit (homComplex A X Y) f).val ⊗ₜ[A]
        (cycleFromUnit (homComplex A Y Z) g).val)) = _
  rw [enrichedComposition_apply]
  simp

/-- Z⁰(Ch(A)) から既存の非有界複体圏への比較関手。 -/
def closedToComplex : ClosedCategory A (Complex A) ⥤ Complex A where
  obj X := ForgetEnrichment.to (Complex A) X
  map f := complexClosedHomEquiv A _ _ f
  map_id X := complexClosedHomEquiv_id A X
  map_comp f g := complexClosedHomEquiv_comp A _ _ _ f g

/-- 比較関手は射に関して忠実。 -/
instance closedToComplexFaithful : (closedToComplex A).Faithful where
  map_injective := by
    intro X Y f g h
    exact (complexClosedHomEquiv A X Y).injective h

/-- 比較関手は射に関して充満。 -/
instance closedToComplexFull : (closedToComplex A).Full where
  map_surjective := (complexClosedHomEquiv A _ _).surjective
/-- 比較関手は対象に関して本質的全射。 -/
instance closedToComplexEssSurj : (closedToComplex A).EssSurj where
  mem_essImage Y := ⟨ForgetEnrichment.of (Complex A) Y, ⟨Iso.refl _⟩⟩

/-- 充満・忠実・本質的全射から比較関手の同値性を登録する。 -/
instance closedToComplexIsEquivalence : (closedToComplex A).IsEquivalence where

/-- 閉次数零圏と既存の非有界複体圏の同値。 -/
def complexClosedEquivalence : ClosedCategory A (Complex A) ≌ Complex A :=
  (closedToComplex A).asEquivalence

/-- 既存の複体の圏構造と dg 豊穣構造を Mathlib の標準クラスで接続する。 -/
instance complexEnrichedOrdinary : EnrichedOrdinaryCategory (Complex A) (Complex A) where
  homEquiv := (complexClosedHomEquiv A _ _).symm
  homEquiv_id X := by
    apply (complexClosedHomEquiv A X X).injective
    change (complexClosedHomEquiv A X X) ((complexClosedHomEquiv A X X).symm (𝟙 X)) =
      complexClosedHomEquiv A X X (𝟙 (ForgetEnrichment.of (Complex A) X))
    rw [Equiv.apply_symm_apply, complexClosedHomEquiv_id]
  homEquiv_comp {X Y Z} f g := by
    apply (complexClosedHomEquiv A X Z).injective
    change complexClosedHomEquiv A X Z ((complexClosedHomEquiv A X Z).symm (f ≫ g)) =
      complexClosedHomEquiv A X Z
      ((complexClosedHomEquiv A X Y).symm f ≫ (complexClosedHomEquiv A Y Z).symm g)
    rw [Equiv.apply_symm_apply, complexClosedHomEquiv_comp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
end SerrePositivity.DifferentialGraded
end

end Examples

/-! ## Components（旧 SerrePositivity/DifferentialGraded/Category/Components.lean） -/

/-! # dg 圏の斉次成分と通常順合成 -/

@[expose] public section Components
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- dg Hom の次数 n の元。Hom 加群の宇宙は u。 -/
abbrev GradedHom (x y : D) (n : ℤ) := (x ⟶[Complex A] y).X n

/-- 微分はコチェイン次数 +1。 -/
abbrev differential {x y : D} {n : ℤ} (f : GradedHom A x y n) : GradedHom A x y (n + 1) :=
  (x ⟶[Complex A] y).d n (n + 1) f

/-- 豊穣順の斉次成分。第一引数が先に作用する f。 -/
def forward {x y z : D} {p q n : ℤ} (f : GradedHom A x y p) (g : GradedHom A y z q)
    (h : p + q = n) : GradedHom A x z n :=
  (eComp (Complex A) x y z).f n
    (ιTensorObj (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q n h (f ⊗ₜ[A] g))

/-- 通常順 μ(g,f)=g∘f。豊穣順へ Koszul 符号を掛けて定義する。 -/
def compose {x y z : D} {p q n : ℤ} (g : GradedHom A y z q) (f : GradedHom A x y p)
    (h : p + q = n) : GradedHom A x z n := (p * q).negOnePow • forward A f g h

/-- 豊穣順と通常順の Koszul 比較。二度の交換の符号は消える。 -/
lemma forward_eq_signed_compose {x y z : D} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (h : p + q = n) :
    forward A f g h = (p * q).negOnePow • compose A g f h := by
  simp [compose, smul_smul]

/-- 豊穣順の微分は tensor 第一因子 p による Leibniz 則。 -/
lemma differential_forward {x y z : D} {p q n : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (h : p + q = n) :
    differential A (forward A f g h) =
      forward A (differential A f) g (by omega) +
      p.negOnePow • forward A f (differential A g) (by omega) := by
  subst n
  have hd := SerrePositivity.cochainTensorι_d (x ⟶[Complex A] y) (y ⟶[Complex A] z) p q
  have hc := (eComp (Complex A) x y z).comm (p + q) (p + q + 1)
  change (eComp (Complex A) x y z).f (p + q) ≫ (x ⟶[Complex A] z).d _ _ =
    (SerrePositivity.cochainTensor (x ⟶[Complex A] y) (y ⟶[Complex A] z)).d _ _ ≫
      (eComp (Complex A) x y z).f (p + q + 1) at hc
  have he := congrArg (fun l => l ≫ (eComp (Complex A) x y z).f (p + q + 1)) hd
  rw [Category.assoc, ← hc] at he
  rw [Preadditive.add_comp, Linear.units_smul_comp] at he
  apply_fun (fun l => l.hom (f ⊗ₜ[A] g)) at he
  change differential A (forward A f g rfl) = _ at he
  change differential A (forward A f g rfl) =
    forward A (n := p + q + 1) (differential A f) g (by omega) +
    p.negOnePow • forward A (n := p + q + 1) f (differential A g) (by omega) at he
  exact he

/-- 通常順の微分。符号は g の次数 q。
整数の符号等式から得られ、標数二の環でも同じ証明が使える。 -/
lemma differential_compose {x y z : D} {p q n : ℤ}
    (g : GradedHom A y z q) (f : GradedHom A x y p) (h : p + q = n) :
    differential A (compose A g f h) =
      compose A (differential A g) f (by omega) +
      q.negOnePow • compose A g (differential A f) (by omega) := by
  unfold compose
  change (x ⟶[Complex A] z).d n (n + 1) ((p * q).negOnePow • forward A f g h) = _
  simp only [Units.smul_def, map_zsmul]
  change (p * q).negOnePow • differential A (forward A f g h) =
    (p * (q + 1)).negOnePow • forward A f (differential A g) (by omega) +
    q.negOnePow • ((p + 1) * q).negOnePow • forward A (differential A f) g (by omega)
  rw [differential_forward]
  simp only [smul_add, smul_smul, ← Int.negOnePow_add]
  have h₁ : p * q + p = p * (q + 1) := by ring
  have h₂ : p * q = q + (p + 1) * q - 2 * q := by ring
  rw [h₁, h₂]
  simp only [Int.negOnePow_sub, Int.negOnePow_two_mul, mul_one]
  abel

/-- 豊穣合成の結合則を斉次元へ降ろす。 -/
lemma forward_assoc {w x y z : D} {p q r n : ℤ}
    (f : GradedHom A w x p) (g : GradedHom A x y q) (h : GradedHom A y z r)
    (hn : p + q + r = n) :
    forward A (forward A f g rfl) h hn =
      forward A f (forward A g h rfl) (by omega) := by
  have he := e_assoc' (Complex A) w x y z
  have he' := congrArg (fun l => l.f n) he
  have hi := congrArg (fun l =>
    (ιTensorObj (w ⟶[Complex A] x) (x ⟶[Complex A] y) p q (p + q) rfl ▷
        (y ⟶[Complex A] z).X r) ≫
      ιTensorObj ((w ⟶[Complex A] x) ⊗ (x ⟶[Complex A] y))
        (y ⟶[Complex A] z) (p + q) r n hn ≫ l) he'
  simp only [HomologicalComplex.comp_f] at hi
  rw [ι_associator_assoc, ι_whiskerLeft_assoc, ι_whiskerRight_assoc] at hi
  have hv := congrArg (fun l => l.hom (f ⊗ₜ[A] g ⊗ₜ[A] h)) hi
  exact hv.symm

/-- 中間和次数を別名にした斉次合成の結合則。 -/
lemma forward_assoc_of_sum {w x y z : D} {p q r a b n : ℤ}
    (f : GradedHom A w x p) (g : GradedHom A x y q) (h : GradedHom A y z r)
    (ha : p + q = a) (hb : q + r = b) (hn : a + r = n) :
    forward A (forward A f g ha) h hn =
      forward A f (forward A g h hb) (by omega) := by
  subst a b
  exact forward_assoc A f g h hn

/-- 通常順の結合則。Koszul 符号の指数は両側で同じ。 -/
lemma compose_assoc {w x y z : D} {p q r n : ℤ}
    (f : GradedHom A w x p) (g : GradedHom A x y q) (h : GradedHom A y z r)
    (hn : p + q + r = n) :
    compose A h (compose A g f rfl) hn =
      compose A (compose A h g rfl) f (by omega) := by
  unfold compose forward
  simp only [Units.smul_def, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_zsmul, smul_smul]
  change (((p + q) * r).negOnePow * (p * q).negOnePow) •
    forward A (forward A f g rfl) h hn =
    ((p * (q + r)).negOnePow * (q * r).negOnePow) •
      forward A f (forward A g h rfl) (by omega)
  rw [forward_assoc]
  simp only [← Int.negOnePow_add]
  congr 1
  congr 1
  ring
/-- dg 単位の閉次数零元。 -/
def unitElement (x : D) : zeroCycles (x ⟶[Complex A] x) :=
  cycleFromUnit _ (eId (Complex A) x)

/-- dg 単位は閉じている。 -/
lemma differential_unit (x : D) : differential A (unitElement A x).val = 0 :=
  (unitElement A x).property

/-- 斉次成分上の左単位則。 -/
lemma forward_unit {x y : D} {n : ℤ} (f : GradedHom A x y n) :
    forward A (unitElement A x).val f (zero_add n) = f := by
  have he := e_id_comp (Complex A) x y
  have he' := congrArg (fun l => l.f n) he
  change (leftUnitor' (x ⟶[Complex A] y)).inv n ≫
    (eId (Complex A) x ▷ (x ⟶[Complex A] y)).f n ≫ (eComp (Complex A) x x y).f n = 𝟙 _ at he'
  rw [leftUnitor'_inv, Category.assoc, Category.assoc, ι_whiskerRight_assoc] at he'
  exact congr($(he').hom f)

/-- 斉次成分上の右単位則。 -/
lemma unit_forward {x y : D} {n : ℤ} (f : GradedHom A x y n) :
    forward A f (unitElement A y).val (add_zero n) = f := by
  have he := e_comp_id (Complex A) x y
  have he' := congrArg (fun l => l.f n) he
  change (rightUnitor' (x ⟶[Complex A] y)).inv n ≫
    ((x ⟶[Complex A] y) ◁ eId (Complex A) y).f n ≫ (eComp (Complex A) x y y).f n = 𝟙 _ at he'
  rw [rightUnitor'_inv, Category.assoc, Category.assoc, ι_whiskerLeft_assoc] at he'
  exact congr($(he').hom f)

/-- 通常順の左単位則。 -/
lemma compose_unit {x y : D} {n : ℤ} (f : GradedHom A x y n) :
    compose A f (unitElement A x).val (zero_add n) = f := by
  simp [compose, forward_unit]

/-- 通常順の右単位則。 -/
lemma unit_compose {x y : D} {n : ℤ} (f : GradedHom A x y n) :
    compose A (unitElement A y).val f (add_zero n) = f := by
  simp [compose, unit_forward]
end SerrePositivity.DifferentialGraded
end

end Components

/-! ## Comparison（旧 SerrePositivity/DifferentialGraded/Category/Comparison.lean） -/

/-! # Ch(A) の境界商と既存の chain homotopy の比較 -/

@[expose] public section Comparison
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- Ch(A) の dg 境界関係は、既存 chain map の通常のホモトピー関係に一致する。 -/
lemma complex_boundary_iff (X Y : Complex A)
    (f g : ForgetEnrichment.of (Complex A) X ⟶ ForgetEnrichment.of (Complex A) Y) :
    boundaryRelation A (Complex A) f g ↔
      Nonempty (Homotopy (complexClosedHomEquiv A X Y f) (complexClosedHomEquiv A X Y g)) := by
  rw [boundaryRelation, unit_homotopy_boundary]
  constructor
  · rintro ⟨h, dh⟩
    apply Nonempty.intro
    refine (Cochain.equivHomotopy _ _).symm ⟨h, ?_⟩
    rw [complexClosedHomEquiv_cochain, complexClosedHomEquiv_cochain]
    change _ = (homComplex A X Y).d (-1) 0 h + _
    change (homComplex A X Y).d (-1) 0 h =
      (cycleFromUnit (homComplex A X Y) f).val -
        (cycleFromUnit (homComplex A X Y) g).val at dh
    rw [dh]
    abel
  · rintro ⟨h⟩
    refine ⟨Cochain.ofHomotopy h, ?_⟩
    change δ (-1) 0 (Cochain.ofHomotopy h) = _
    rw [δ_ofHomotopy, complexClosedHomEquiv_cochain, complexClosedHomEquiv_cochain]
    rfl

/-- H⁰(Ch(A)) での等式は既存の chain homotopy と同値。 -/
lemma complex_H0_eq_iff (X Y : Complex A)
    (f g : ForgetEnrichment.of (Complex A) X ⟶ ForgetEnrichment.of (Complex A) Y) :
    (toHomotopy A (Complex A)).map f = (toHomotopy A (Complex A)).map g ↔
      Nonempty (Homotopy (complexClosedHomEquiv A X Y f) (complexClosedHomEquiv A X Y g)) := by
  rw [toHomotopy_map_eq_iff, complex_boundary_iff]
end SerrePositivity.DifferentialGraded
end

end Comparison

/-! ## HomTransport（旧 SerrePositivity/DifferentialGraded/Category/HomTransport.lean） -/

/-!
概要：Hom 複体の同型に沿って dg 圏の単位・合成・三法則を移す。
方針：全 Hom の指定同型で合成を共役し、元の三法則を単射性で反映する。
規約：対象ラベルを保持し、既存の dg 圏を変更しない。
使われ方：係数閉包の各 Hom を固定自由加群の商による提示へ符号化する。
-/

@[expose] public section HomTransport
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (H : D → D → Complex R) (e : ∀ x y, H x y ≅ homObject R D x y)

lemma dgHomTransport_left (x y : D) :
    (λ_ (H x y)).inv ≫ (eId (Complex R) x ≫ (e x x).inv) ▷ H x y ≫
      ((e x x).hom ⊗ₘ (e x y).hom) ≫ eComp (Complex R) x x y ≫ (e x y).inv = 𝟙 _ := by
  apply (cancel_mono (e x y).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [whiskerRight_comp_tensorHom_assoc]
  simp only [Iso.inv_hom_id, Category.assoc, Category.comp_id]
  rw [leftUnitor_inv_comp_tensorHom_assoc, e_id_comp]
  simp

lemma dgHomTransport_right (x y : D) :
    (ρ_ (H x y)).inv ≫ H x y ◁ (eId (Complex R) y ≫ (e y y).inv) ≫
      ((e x y).hom ⊗ₘ (e y y).hom) ≫ eComp (Complex R) x y y ≫ (e x y).inv = 𝟙 _ := by
  apply (cancel_mono (e x y).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [whiskerLeft_comp_tensorHom_assoc]
  simp only [Iso.inv_hom_id, Category.assoc, Category.comp_id]
  rw [rightUnitor_inv_comp_tensorHom_assoc, e_comp_id]
  simp

lemma dgHomTransport_assoc (w x y z : D) :
    (α_ (H w x) (H x y) (H y z)).inv ≫
      (((e w x).hom ⊗ₘ (e x y).hom) ≫ eComp (Complex R) w x y ≫ (e w y).inv) ▷ H y z ≫
      ((e w y).hom ⊗ₘ (e y z).hom) ≫ eComp (Complex R) w y z ≫ (e w z).inv =
    H w x ◁ (((e x y).hom ⊗ₘ (e y z).hom) ≫
      eComp (Complex R) x y z ≫ (e x z).inv) ≫
      ((e w x).hom ⊗ₘ (e x z).hom) ≫ eComp (Complex R) w x z ≫ (e w z).inv := by
  apply (cancel_mono (e w z).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    whiskerRight_comp_tensorHom_assoc, whiskerLeft_comp_tensorHom_assoc]
  rw [← tensorHom_comp_whiskerRight_assoc, ← associator_inv_naturality_assoc, e_assoc]
  rw [← tensorHom_comp_whiskerLeft_assoc]

@[instance_reducible] def dgCategoryHomTransport : DGCategory R D :=
  ofHomObjects R D H
    (fun x => eId (Complex R) x ≫ (e x x).inv)
    (fun x y z => ((e x y).hom ⊗ₘ (e y z).hom) ≫
      eComp (Complex R) x y z ≫ (e x z).inv)
    (dgHomTransport_left R D H e) (dgHomTransport_right R D H e)
    (dgHomTransport_assoc R D H e)

end SerrePositivity.DifferentialGraded
end

end HomTransport

/-! ## LocalizationHom（旧 SerrePositivity/DifferentialGraded/Category/LocalizationHom.lean） -/

/-! # 準同型を反転するcoyonedaと局所化のHom

Homの宇宙は局所化前後で独立。ULiftで値域をそろえ、局所化の普遍性のみを使う。
-/

@[expose] public section LocalizationHom
universe u₁ u₂ v₁ v₂

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.LocalizationHom
open CategoryTheory Opposite
variable {C : Type u₁} [Category.{v₁} C] {E : Type u₂} [Category.{v₂} E]
variable (W : MorphismProperty C) (L : C ⥤ E) [L.IsLocalization W] (P : C)

abbrev source : C ⥤ Type (max v₁ v₂) := uliftCoyoneda.{v₂}.obj (op P)
abbrev target : E ⥤ Type (max v₁ v₂) := uliftCoyoneda.{v₁}.obj (op (L.obj P))

variable (hP : W.IsInvertedBy (coyoneda.obj (op P)))

include hP in
lemma source_inverts : W.IsInvertedBy (uliftCoyoneda.{v₂}.obj (op P)) := by
  intro X Y f hf
  have : IsIso ((coyoneda.obj (op P)).map f) := hP f hf
  change IsIso (uliftFunctor.{v₂}.map ((coyoneda.obj (op P)).map f))
  infer_instance

def model : E ⥤ Type (max v₁ v₂) :=
  Localization.lift (source P) (source_inverts W P hP) L

def fac : L ⋙ model W L P hP ≅ source P :=
  Localization.fac (source P) (source_inverts W P hP) L

def sourceMap : source P ⟶ L ⋙ target L P where
  app X := ↾fun f => ULift.up (L.map f.down)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro g
    change ULift.up (L.map (g.down ≫ f)) = ULift.up (L.map g.down ≫ L.map f)
    exact congrArg ULift.up (L.map_comp g.down f)

def comparison : model W L P hP ⟶ target L P :=
  (Localization.whiskeringLeftFunctor' L W (Type (max v₁ v₂))).preimage
    ((fac W L P hP).hom ≫ sourceMap L P)

lemma comparison_fac :
    Functor.whiskerLeft L (comparison W L P hP) =
      (fac W L P hP).hom ≫ sourceMap L P :=
  (Localization.whiskeringLeftFunctor' L W (Type (max v₁ v₂))).map_preimage _

def identityElement : (model W L P hP).obj (L.obj P) :=
  (fac W L P hP).inv.app P (ULift.up (𝟙 P))

lemma comparison_identity :
    (comparison W L P hP).app (L.obj P) (identityElement W L P hP) = ULift.up (𝟙 (L.obj P)) := by
  have h := congrArg (fun a => a (identityElement W L P hP))
    (congr_app (comparison_fac W L P hP) P)
  change (comparison W L P hP).app (L.obj P) (identityElement W L P hP) =
    ULift.up (L.map (((fac W L P hP).hom.app P
      ((fac W L P hP).inv.app P (ULift.up (𝟙 P)))).down)) at h
  have he := congrArg (fun a => a (ULift.up (𝟙 P)))
    (congr_app (fac W L P hP).inv_hom_id P)
  change (fac W L P hP).hom.app P ((fac W L P hP).inv.app P (ULift.up (𝟙 P))) = ULift.up (𝟙 P) at he
  rw [he, _root_.CategoryTheory.Functor.map_id] at h
  exact h

def inverseComparison : target L P ⟶ model W L P hP where
  app X := ↾fun g => (model W L P hP).map g.down (identityElement W L P hP)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro g
    change (model W L P hP).map (g.down ≫ f) (identityElement W L P hP) =
      (model W L P hP).map f ((model W L P hP).map g.down (identityElement W L P hP))
    rw [Functor.map_comp]
    rfl

lemma inverseComparison_comparison :
    inverseComparison W L P hP ≫ comparison W L P hP = 𝟙 (target L P) := by
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  intro g
  have h := congrArg (fun a => a (identityElement W L P hP))
    ((comparison W L P hP).naturality g.down)
  change (comparison W L P hP).app X
      ((model W L P hP).map g.down (identityElement W L P hP)) =
    ULift.up (((comparison W L P hP).app (L.obj P) (identityElement W L P hP)).down ≫ g.down) at h
  rw [comparison_identity] at h
  change (comparison W L P hP).app X
    ((model W L P hP).map g.down (identityElement W L P hP)) = g
  simpa only [Category.id_comp, ULift.up_down] using h

lemma comparison_inverseComparison :
    comparison W L P hP ≫ inverseComparison W L P hP = 𝟙 (model W L P hP) := by
  apply Localization.natTrans_ext L W
  intro X
  apply ConcreteCategory.hom_ext
  intro x
  have hc := congrArg (fun a => a x) (congr_app (comparison_fac W L P hP) X)
  change (comparison W L P hP).app (L.obj X) x =
    ULift.up (L.map (((fac W L P hP).hom.app X x).down)) at hc
  change (model W L P hP).map (((comparison W L P hP).app (L.obj X) x).down)
    (identityElement W L P hP) = x
  rw [hc]
  let g := ((fac W L P hP).hom.app X x).down
  have hn := congrArg (fun a => a (ULift.up (𝟙 P))) ((fac W L P hP).inv.naturality g)
  dsimp [source, uliftCoyoneda, uliftYoneda, yoneda, uliftFunctor, identityElement] at hn
  simp only [Category.id_comp] at hn
  change (fac W L P hP).inv.app X (ULift.up g) =
    (model W L P hP).map (L.map g) (identityElement W L P hP) at hn
  rw [← hn]
  exact congrArg (fun a => a x) (congr_app (fac W L P hP).hom_inv_id X)

def homEquiv (X : E) : (L.obj P ⟶ X) ≃ (model W L P hP).obj X where
  toFun f := (model W L P hP).map f (identityElement W L P hP)
  invFun x := ((comparison W L P hP).app X x).down
  left_inv f := by
    have h := congrArg (fun a => a (ULift.up f))
      (congr_app (inverseComparison_comparison W L P hP) X)
    exact congrArg ULift.down h
  right_inv x :=
    congrArg (fun a => a x) (congr_app (comparison_inverseComparison W L P hP) X)

def mapEquiv (X : C) : (P ⟶ X) ≃ (L.obj P ⟶ L.obj X) :=
  Equiv.ulift.symm.trans (((fac W L P hP).app X).symm.toEquiv.trans
    (homEquiv W L P hP (L.obj X)).symm)

lemma mapEquiv_apply (X : C) (f : P ⟶ X) : mapEquiv W L P hP X f = L.map f := by
  have h := congrArg (fun a => a ((fac W L P hP).inv.app X (ULift.up f)))
    (congr_app (comparison_fac W L P hP) X)
  change (comparison W L P hP).app (L.obj X) ((fac W L P hP).inv.app X (ULift.up f)) =
    ULift.up (L.map (((fac W L P hP).hom.app X
      ((fac W L P hP).inv.app X (ULift.up f))).down)) at h
  have he := congrArg (fun a => a (ULift.up f))
    (congr_app (fac W L P hP).inv_hom_id X)
  change (fac W L P hP).hom.app X ((fac W L P hP).inv.app X (ULift.up f)) = ULift.up f at he
  rw [he] at h
  exact congrArg ULift.down h

include hP in
lemma map_bijective (X : C) : Function.Bijective (L.map (X := P) (Y := X)) := by
  have h : (fun f : P ⟶ X => mapEquiv W L P hP X f) = L.map := by
    funext f
    exact mapEquiv_apply W L P hP X f
  rw [← h]
  exact (mapEquiv W L P hP X).bijective

end SerrePositivity.DifferentialGraded.LocalizationHom
end

end LocalizationHom

/-! ## TriangleComparison（旧 SerrePositivity/DifferentialGraded/Category/TriangleComparison.lean） -/

/-! # dg標準三角形の比較に使う第三射の評価 -/

@[expose] public section TriangleComparison
universe u v u' v'

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [HasShift C ℤ] [HasShift D ℤ]

/-- 第三射の計算式を、shift整合関手が誘導する三角形の第三射の計算式へ運ぶ。 -/
lemma triangleComparison_mor₃ (F : C ⥤ D) [F.CommShift ℤ] (T : Triangle C)
    (f : T.obj₃ ⟶ T.obj₁⟦(1 : ℤ)⟧) (h : T.mor₃ = f) :
    (F.mapTriangle.obj T).mor₃ = F.map f ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁ :=
  congrArg (fun a => F.map a ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) h

end SerrePositivity.DifferentialGraded
end

end TriangleComparison

/-! ## QuotientComparison（旧 SerrePositivity/DifferentialGraded/Category/QuotientComparison.lean） -/

/-! # 境界商の比較自然同型の代表上の計算

実際の大きいdg加群構成を展開せず、商・関手等式・右whiskeringを抽象的に評価する。
-/

@[expose] public section QuotientComparison
universe u v u' v' u'' v''

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E]
  {D : Type u''} [Category.{v''} D]

/-- 商へ降ろした、関手等式と右whiskeringを含む比較を元の代表で評価する。 -/
lemma quotientComparison_hom_app (r : HomRel C)
    (F G : Quotient r ⥤ D) (U V : C ⥤ E) (J : E ⥤ D)
    (h₁ : Quotient.functor r ⋙ F = U ⋙ J) (h₂ : U = V)
    (e : V ⋙ J ≅ Quotient.functor r ⋙ G) (X : C) :
    (Quotient.natIsoLift r
      (eqToIso h₁ ≪≫ Functor.isoWhiskerRight (eqToIso h₂) J ≪≫ e)).hom.app
        ((Quotient.functor r).obj X) =
      eqToHom (congrArg (fun H : C ⥤ D => H.obj X) h₁) ≫
        J.map (eqToHom (congrArg (fun H : C ⥤ E => H.obj X) h₂)) ≫ e.hom.app X := by
  simp [Quotient.natIsoLift, eqToHom_app]

/-- 関手等式の後の左whiskeringを対象で評価し、等式輸送を対象の等式へ落とす。 -/
lemma comparisonWhiskerLeft_hom_app (F : C ⥤ D) (I : C ⥤ E) (U V : E ⥤ D)
    (h : F = I ⋙ U) (e : U ≅ V) (X : C) :
    (eqToIso h ≪≫ Functor.isoWhiskerLeft I e).hom.app X =
      eqToHom (congrArg (fun H : C ⥤ D => H.obj X) h) ≫ e.hom.app (I.obj X) := by
  simp [eqToHom_app]

/-- 結合子で括弧を揃えて二つの比較を合成すると、成分は写像した第一成分と第二成分の合成になる。 -/
lemma comparisonCompose_hom_app (S : C ⥤ C) (I : C ⥤ E) (L : E ⥤ D)
    (K : E ⥤ E) (T : D ⥤ D) (a : S ⋙ I ≅ I ⋙ K) (b : K ⋙ L ≅ L ⋙ T) (X : C) :
    ((Functor.associator S I L).symm ≪≫ Functor.isoWhiskerRight a L ≪≫
      Functor.associator I K L ≪≫ Functor.isoWhiskerLeft I b ≪≫
      (Functor.associator I L T).symm).hom.app X =
        L.map (a.hom.app X) ≫ b.hom.app (I.obj X) := by
  simp

end SerrePositivity.DifferentialGraded
end

end QuotientComparison

/-! ## IdempotentTelescope（旧 SerrePositivity/DifferentialGraded/Category/IdempotentTelescope.lean） -/

/-! # 可算余積による冪等射の分裂

冪等射を遷移射とする可算列のtelescopeを用いる。最初の射の左逆は
各余積成分上で有限和として明示し、一般の余極限の完全性は仮定しない。
-/

@[expose] public section IdempotentTelescope
universe v u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Category Limits Preadditive Pretriangulated
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (X : C) [HasCoproduct (fun _ : ℕ => X)] (p : X ⟶ X)

def idempotentTelescopeShift : (∐ fun _ : ℕ => X) ⟶ (∐ fun _ : ℕ => X) :=
  Sigma.desc (fun n => p ≫ Sigma.ι (fun _ : ℕ => X) (n + 1))

def idempotentTelescopeMap : (∐ fun _ : ℕ => X) ⟶ (∐ fun _ : ℕ => X) :=
  𝟙 _ - idempotentTelescopeShift X p

def idempotentTelescopeRetraction : (∐ fun _ : ℕ => X) ⟶ (∐ fun _ : ℕ => X) :=
  Sigma.desc (fun n =>
    -(∑ k ∈ Finset.range n, p ≫ Sigma.ι (fun _ : ℕ => X) k) +
      (𝟙 X - p) ≫ Sigma.ι (fun _ : ℕ => X) n)

lemma idempotentTelescopeMap_retraction (hp : p ≫ p = p) :
    idempotentTelescopeMap X p ≫ idempotentTelescopeRetraction X p = 𝟙 _ := by
  apply Sigma.hom_ext
  intro n
  have hpp {Z : C} (f : X ⟶ Z) : p ≫ p ≫ f = p ≫ f := by
    rw [← Category.assoc, hp]
  simp only [idempotentTelescopeMap, idempotentTelescopeShift,
    idempotentTelescopeRetraction, comp_sub, comp_id, sub_comp, Category.assoc,
    Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc, comp_add, comp_neg, comp_sum,
    hpp, id_comp, Finset.sum_range_succ]
  abel

lemma idempotentTelescopeMap_mono (hp : p ≫ p = p) :
    Mono (idempotentTelescopeMap X p) := by
  constructor
  intro Z f g h
  have := congrArg (fun k => k ≫ idempotentTelescopeRetraction X p) h
  simpa only [Category.assoc, idempotentTelescopeMap_retraction X p hp, comp_id] using this

variable [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A countable coproduct of copies of the source suffices to split an idempotent. -/
theorem idempotent_split_of_countable_coproduct (hp : p ≫ p = p) :
    ∃ (Y : C) (i : Y ⟶ X) (e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p := by
  let d : (∐ fun _ : ℕ => X) ⟶ X := Sigma.desc (fun _ => p)
  have had : idempotentTelescopeMap X p ≫ d = 0 := by
    apply Sigma.hom_ext
    intro n
    simp only [idempotentTelescopeMap, idempotentTelescopeShift, d, comp_sub,
      sub_comp, Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc, id_comp]
    rw [hp, sub_self, comp_zero]
  obtain ⟨Y, c, h, hT⟩ := distinguished_cocone_triangle (idempotentTelescopeMap X p)
  have hh := Triangle.mor₃_eq_zero_of_mono₁ _ hT
    (idempotentTelescopeMap_mono X p hp)
  have : Epi c := Triangle.epi₂ _ hT hh
  obtain ⟨r, hr⟩ := Triangle.yoneda_exact₂ _ hT d had
  change d = c ≫ r at hr
  have hac : idempotentTelescopeMap X p ≫ c = 0 :=
    comp_distTriang_mor_zero₁₂ _ hT
  have hc (n : ℕ) : Sigma.ι (fun _ : ℕ => X) n ≫ c =
      p ≫ Sigma.ι (fun _ : ℕ => X) (n + 1) ≫ c := by
    have hn := congrArg (fun k => Sigma.ι (fun _ : ℕ => X) n ≫ k) hac
    simpa only [idempotentTelescopeMap, idempotentTelescopeShift, comp_sub, comp_id,
      sub_comp, Category.assoc, Sigma.ι_comp_desc_assoc, id_comp, comp_zero, sub_eq_zero] using hn
  have hpc (n : ℕ) : p ≫ Sigma.ι (fun _ : ℕ => X) n ≫ c =
      Sigma.ι (fun _ : ℕ => X) n ≫ c := by
    calc
      _ = p ≫ p ≫ Sigma.ι (fun _ : ℕ => X) (n + 1) ≫ c := by rw [← hc n]
      _ = _ := by rw [← Category.assoc p p, hp, ← hc n]
  have hconstant (n : ℕ) : Sigma.ι (fun _ : ℕ => X) n ≫ c =
      Sigma.ι (fun _ : ℕ => X) 0 ≫ c := by
    induction n with
    | zero => rfl
    | succ n ih => rw [← hpc (n + 1), ← hc n, ih]
  refine ⟨Y, r, Sigma.ι (fun _ : ℕ => X) 0 ≫ c, ?_, ?_⟩
  · apply (cancel_epi c).1
    simp only [← Category.assoc, comp_id]
    rw [← hr]
    apply Sigma.hom_ext
    intro n
    simp only [Category.assoc, d, Sigma.ι_comp_desc_assoc]
    rw [hpc 0, hconstant n]
  · rw [Category.assoc, ← hr]
    exact Sigma.ι_comp_desc _ _

end SerrePositivity.DifferentialGraded
end

end IdempotentTelescope

/-! ## TriangulatedTransport（旧 SerrePositivity/DifferentialGraded/Category/TriangulatedTransport.lean） -/

/-! # dg enhancementのH⁰比較に使う三角構造の移送

与えたshiftとその比較を維持し、完全忠実同値でdistinguished三角形を引き戻す。
モデル構造・局所化・dg enhancement自体の存在を仮定する補助APIではない。
-/

@[expose] public section TriangulatedTransport
universe u v u' v'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
open scoped ZeroObject
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- 同値の逆関手で零対象を選び、完全忠実性で零性を反映する。 -/
theorem dgComparisonHasZeroObject (e : C ≌ D) [HasZeroObject D] : HasZeroObject C := by
  have hz : IsZero (e.functor.obj (e.inverse.obj (0 : D))) :=
    (isZero_zero D).of_iso (e.counitIso.app (0 : D))
  exact (IsZero.of_full_of_faithful_of_isZero e.functor _ hz).hasZeroObject

variable [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
  [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- 既存のshiftを保った同値で三角構造を引き戻す。各公理を対象側の公理から証明する。 -/
@[instance_reducible]
def dgComparisonPretriangulated (e : C ≌ D) [e.functor.CommShift ℤ] [e.functor.Additive] :
    Pretriangulated C where
  distinguishedTriangles := {T | e.functor.mapTriangle.obj T ∈ distTriang D}
  isomorphic_distinguished T₁ hT₁ T₂ a :=
    isomorphic_distinguished _ hT₁ _ (e.functor.mapTriangle.mapIso a)
  contractible_distinguished X := by
    let F := e.functor
    have hz : IsZero (F.obj (0 : C)) := F.map_isZero (isZero_zero C)
    apply isomorphic_distinguished _ (contractible_distinguished (F.obj X))
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) hz.isoZero
      (by simp [Functor.mapTriangle, contractibleTriangle, F])
      (by simp [Functor.mapTriangle, contractibleTriangle, F])
      (by simp [Functor.mapTriangle, contractibleTriangle, F])
  distinguished_cocone_triangle {X Y} f := by
    let F := e.functor
    obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (F.map f)
    let Z' := e.inverse.obj Z
    let z : F.obj Z' ≅ Z := e.counitIso.app Z
    let g' : Y ⟶ Z' := F.preimage (g ≫ z.inv)
    let h' : Z' ⟶ X⟦(1 : ℤ)⟧ :=
      F.preimage (z.hom ≫ h ≫ (F.commShiftIso (1 : ℤ)).inv.app X)
    refine ⟨Z', g', h', isomorphic_distinguished _ hT _ ?_⟩
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) z
      (by simp [Functor.mapTriangle, F])
      (by simp [Functor.mapTriangle, F, g'])
      (by simp [Functor.mapTriangle, F, h', Category.assoc])
  rotate_distinguished_triangle T :=
    (rotate_distinguished_triangle (e.functor.mapTriangle.obj T)).trans
      (distinguished_iff_of_iso ((e.functor.mapTriangleRotateIso).app T))
  complete_distinguished_triangle_morphism T₁ T₂ hT₁ hT₂ a b hab := by
    let F := e.functor
    have hf : (F.mapTriangle.obj T₁).mor₁ ≫ F.map b =
        F.map a ≫ (F.mapTriangle.obj T₂).mor₁ := by
      change F.map T₁.mor₁ ≫ F.map b = F.map a ≫ F.map T₂.mor₁
      simpa only [F.map_comp] using congrArg F.map hab
    obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism
      (F.mapTriangle.obj T₁) (F.mapTriangle.obj T₂) hT₁ hT₂ (F.map a) (F.map b) hf
    refine ⟨F.preimage c, F.map_injective ?_, F.map_injective ?_⟩
    · change F.map T₁.mor₂ ≫ c = F.map b ≫ F.map T₂.mor₂ at hc₂
      simpa only [F.map_comp, F.map_preimage] using hc₂
    · change (F.map T₁.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T₁.obj₁) ≫
        (F.map a)⟦(1 : ℤ)⟧' = c ≫ F.map T₂.mor₃ ≫
          (F.commShiftIso (1 : ℤ)).hom.app T₂.obj₁ at hc₃
      rw [← cancel_mono ((F.commShiftIso (1 : ℤ)).hom.app T₂.obj₁)]
      simpa only [F.map_comp, F.map_preimage, Category.assoc,
        Functor.commShiftIso_hom_naturality] using hc₃

end SerrePositivity.DifferentialGraded
end

end TriangulatedTransport

/-! ## EquivalenceComparison（旧 SerrePositivity/DifferentialGraded/Category/EquivalenceComparison.lean） -/

/-! # 同値による実現比較の成分計算 -/

@[expose] public section EquivalenceComparison
universe v u v' u'

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- 逆関手で戻してunitの逆を合成した射を送り直すと、counitによる自然な比較となる。 -/
lemma equivalence_map_inverse_then_unit (E : C ≌ D) {Y : D} {X : C}
    (f : Y ⟶ E.functor.obj X) :
    E.functor.map (E.inverse.map f ≫ E.unitIso.inv.app X) = E.counitIso.hom.app Y ≫ f := by
  rw [Functor.map_comp, ← E.counit_app_functor]
  exact E.counit_naturality f

/-- 同値による実現のfactor比較を送り直した自然変換の抽象的な計算。 -/
lemma equivalenceExtension_factor_whisker {B S : Type*} [Category* B] [Category* S]
    (L : B ⥤ S) (H : S ⥤ D) (F : B ⥤ C) (E : C ≌ D)
    (α : L ⋙ H ≅ F ⋙ E.functor) :
    Functor.whiskerRight
      ((Functor.associator L H E.inverse).symm ≪≫
        Functor.isoWhiskerRight α E.inverse ≪≫ Functor.associator F E.functor E.inverse ≪≫
        Functor.isoWhiskerLeft F E.unitIso.symm ≪≫ Functor.rightUnitor F).hom E.functor =
    (Functor.associator L (H ⋙ E.inverse) E.functor).hom ≫
      Functor.whiskerLeft L
        (Functor.associator H E.inverse E.functor ≪≫
          Functor.isoWhiskerLeft H E.counitIso ≪≫ Functor.rightUnitor H).hom ≫ α.hom := by
  apply NatTrans.ext
  funext X
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map,
    Category.id_comp, Category.comp_id] using
    (equivalence_map_inverse_then_unit E (α.hom.app X))

end SerrePositivity.DifferentialGraded

end EquivalenceComparison

/-! ## FaithfulHomConstruction（旧 SerrePositivity/DifferentialGraded/Category/FaithfulHomConstruction.lean） -/

/-!
概要：単位・合成と両立する単射 Hom 比較から dg 圏の三法則を反映する。
方針：各法則を忠実な Hom 鎖写像で後合成し、元の豊穣圏の法則へ帰着する。
規約：比較写像の同型性は要求せず、構造射の両立を明示入力とする。
使われ方：c′ の微分・合成で閉じた係数 submodule 族から実 dg 圏を構成する。
-/

@[expose] public section FaithfulHomConstruction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (H : D → D → Complex R) (ι : ∀ x y, H x y ⟶ homObject R D x y)
  [∀ x y, Mono (ι x y)] (unit : ∀ x, 𝟙_ (Complex R) ⟶ H x x)
  (comp : ∀ x y z, H x y ⊗ H y z ⟶ H x z)
  (hu : ∀ x, unit x ≫ ι x x = eId (Complex R) x)
  (hc : ∀ x y z, comp x y z ≫ ι x z =
    (ι x y ⊗ₘ ι y z) ≫ eComp (Complex R) x y z)

include ι hu hc in
lemma dgFaithfulHom_left (x y : D) :
    (λ_ (H x y)).inv ≫ unit x ▷ H x y ≫ comp x x y = 𝟙 _ := by
  apply (cancel_mono (ι x y)).1
  simp only [Category.assoc, hc, Category.id_comp]
  rw [whiskerRight_comp_tensorHom_assoc, hu,
    leftUnitor_inv_comp_tensorHom_assoc, e_id_comp]
  simp

include ι hu hc in
lemma dgFaithfulHom_right (x y : D) :
    (ρ_ (H x y)).inv ≫ H x y ◁ unit y ≫ comp x y y = 𝟙 _ := by
  apply (cancel_mono (ι x y)).1
  simp only [Category.assoc, hc, Category.id_comp]
  rw [whiskerLeft_comp_tensorHom_assoc, hu,
    rightUnitor_inv_comp_tensorHom_assoc, e_comp_id]
  simp

include ι hc in
lemma dgFaithfulHom_assoc (w x y z : D) :
    (α_ (H w x) (H x y) (H y z)).inv ≫ comp w x y ▷ H y z ≫ comp w y z =
      H w x ◁ comp x y z ≫ comp w x z := by
  apply (cancel_mono (ι w z)).1
  simp only [Category.assoc, hc, whiskerRight_comp_tensorHom_assoc,
    whiskerLeft_comp_tensorHom_assoc]
  rw [← tensorHom_comp_whiskerRight_assoc, ← associator_inv_naturality_assoc, e_assoc]
  rw [← tensorHom_comp_whiskerLeft_assoc]

@[instance_reducible] def dgCategoryOfFaithfulHomMaps : DGCategory R D :=
  ofHomObjects R D H unit comp
    (dgFaithfulHom_left R D H ι unit comp hu hc)
    (dgFaithfulHom_right R D H ι unit comp hu hc)
    (dgFaithfulHom_assoc R D H ι comp hc)

end SerrePositivity.DifferentialGraded
end

end FaithfulHomConstruction
