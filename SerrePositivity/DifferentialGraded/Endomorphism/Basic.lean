module

public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.DifferentialGraded.Functor.Opposite
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Shift.Quotient
public import SerrePositivity.DifferentialGraded.Module.GradedSplitElements
public import SerrePositivity.DifferentialGraded.Module.YonedaFunctor
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement
public import SerrePositivity.DifferentialGraded.Functor.Components
public import SerrePositivity.DifferentialGraded.Functor.ModuleConeIso
public import SerrePositivity.DifferentialGraded.Module.ConeHomotopyDesc
public import SerrePositivity.DifferentialGraded.Module.EvaluationReflects
public import SerrePositivity.DifferentialGraded.Functor.ModuleShift

/-!
# Endomorphism.Basic

## 概要
11 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## Basic（旧 SerrePositivity/DifferentialGraded/Endomorphism/Basic.lean） -/

/-! # 指定対象の一対象endomorphism dg圏

積の順序は主モデルのforward composition、すなわち Hom(E,E)⊗Hom(E,E) → Hom(E,E)。
対象型をEで添字付けし、異なる指定対象の豊穣構造の衝突を避ける。
-/

@[expose] public section Basic
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 指定対象Eのendomorphism dg代数を一対象dg圏として扱うための対象型。 -/
inductive EndomorphismObject (E : D) : Type
  | point
  deriving DecidableEq, Inhabited

instance (E : D) : Unique (EndomorphismObject E) where
  default := .point
  uniq x := by cases x; rfl

/-- 非有界Hom複体と単位・豊穣合成を指定enhancementからそのまま継承する。 -/
instance endomorphismDGCategory (E : D) : DGCategory A (EndomorphismObject E) :=
  ofHomObjects A _ (fun _ _ => homObject A D E E)
    (fun _ => eId (Complex A) E) (fun _ _ _ => eComp (Complex A) E E E)
    (fun _ _ => EnrichedCategory.id_comp E E)
    (fun _ _ => EnrichedCategory.comp_id E E)
    (fun _ _ _ _ => EnrichedCategory.assoc E E E E)

/-- 一対象dg圏から指定enhancementへの全Homを保つ包含。 -/
def endomorphismInclusion (E : D) : DGFunctor A (EndomorphismObject E) D where
  obj _ := E
  map _ _ := 𝟙 _
  map_id _ := by simp; rfl
  map_comp _ _ _ := by simp; rfl

/-- 一対象のHomはH⁰や導来Endではなく、元の全次数Hom複体である。 -/
lemma endomorphism_hom (E : D) (x y : EndomorphismObject E) :
    homObject A (EndomorphismObject E) x y = homObject A D E E := rfl

/-- 指定対象をdg関手で送るとendomorphismの間のdg関手を得る。 -/
def endomorphismMap {C : Type*} [DGCategory A C] (F : DGFunctor A D C) (E : D) :
    DGFunctor A (EndomorphismObject E) (EndomorphismObject (F.obj E)) where
  obj _ := .point
  map _ _ := F.map E E
  map_id _ := F.map_id E
  map_comp _ _ _ := F.map_comp E E E

/-- End上の写像と元のdg関手の正方形。 -/
lemma endomorphismMap_comp_inclusion {C : Type*} [DGCategory A C]
    (F : DGFunctor A D C) (E : D) :
    (endomorphismMap A F E).comp (endomorphismInclusion A (F.obj E)) =
      (endomorphismInclusion A E).comp F := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [DGFunctor.comp, EnrichedFunctor.comp_map, endomorphismMap,
    endomorphismInclusion, Category.comp_id, eqToHom_refl]

end SerrePositivity.DifferentialGraded
end

end Basic

/-! ## ConeTriangleMapIso（旧 SerrePositivity/DifferentialGraded/Endomorphism/ConeTriangleMapIso.lean） -/

/-! # coneの比較射から三角形比較を組み立てる補助 -/

@[expose] public section ConeTriangleMapIso

namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable {C T : Type*} [Category* C] [Category* T] [HasShift C ℤ] [HasShift T ℤ]

def coneTriangleMapIso (F : C ⥤ T) [F.CommShift ℤ]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
    {Z' : T} (g' : F.obj Y ⟶ Z') (h' : Z' ⟶ (F.obj X)⟦(1 : ℤ)⟧)
    (e : Z' ≅ F.obj Z) (hg : g' ≫ e.hom = F.map g)
    (hh : e.hom ≫ F.map h ≫ (F.commShiftIso (1 : ℤ)).hom.app X = h') :
    Triangle.mk (F.map f) g' h' ≅ F.mapTriangle.obj (Triangle.mk f g h) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    (hg.trans (Category.id_comp _).symm)
    ((congrArg (fun k => h' ≫ k) ((shiftFunctor T (1 : ℤ)).map_id (F.obj X))).trans
      ((Category.comp_id _).trans hh.symm))

end SerrePositivity.DifferentialGraded

end ConeTriangleMapIso

/-! ## LocalizationHomNaturality（旧 SerrePositivity/DifferentialGraded/Endomorphism/LocalizationHomNaturality.lean） -/

/-! # 局所化の生成射からのHom比較の自然性 -/

@[expose] public section LocalizationHomNaturality
universe u₁ v₁ u₂ v₂

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory

/-- 終域側の自然性は局所化前の射について検証すればよい。 -/
lemma localizationHom_naturality_right
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (W : MorphismProperty D) (F : C ⥤ W.Localization) (G : W.Localization ⥤ C)
    (α : ∀ X Y, (F.obj X ⟶ Y) → (X ⟶ G.obj Y))
    (h : ∀ (X : C) {Y Y' : D} (g : Y ⟶ Y') (φ : F.obj X ⟶ W.Q.obj Y),
      α X (W.Q.obj Y') (φ ≫ W.Q.map g) = α X (W.Q.obj Y) φ ≫ G.map (W.Q.map g))
    (X : C) {Y Y' : W.Localization} (g : Y ⟶ Y') (φ : F.obj X ⟶ Y) :
    α X Y' (φ ≫ g) = α X Y φ ≫ G.map g := by
  let P : MorphismProperty W.Localization := fun Y Y' g =>
    ∀ (X : C) (φ : F.obj X ⟶ Y), α X Y' (φ ≫ g) = α X Y φ ≫ G.map g
  have : P.IsStableUnderComposition := ⟨by
      intro _ _ _ f g hf hg X φ
      rw [← Category.assoc, hg, hf, G.map_comp, Category.assoc]⟩
  have hP : P = ⊤ := Localization.Construction.morphismProperty_eq_top' (W := W) P
    (fun {_ _} f => fun X φ => h X f φ) (by
      intro Y Y' e he X φ
      have ht := he X (φ ≫ e.inv)
      simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at ht
      apply (cancel_mono (G.map e.hom)).mp
      rw [Category.assoc, ← G.map_comp, e.inv_hom_id, G.map_id, Category.comp_id]
      exact ht.symm)
  exact (show P g from hP ▸ trivial) X φ

/-- 始域側の自然性も局所化前の射から拡張できる。 -/
lemma localizationHom_naturality_left
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (W : MorphismProperty C) (F : W.Localization ⥤ D) (G : D ⥤ W.Localization)
    (α : ∀ X Y, (F.obj X ⟶ Y) → (X ⟶ G.obj Y))
    (h : ∀ {X X' : C} (f : X ⟶ X') (Y : D) (φ : F.obj (W.Q.obj X') ⟶ Y),
      α (W.Q.obj X) Y (F.map (W.Q.map f) ≫ φ) = W.Q.map f ≫ α (W.Q.obj X') Y φ)
    {X X' : W.Localization} (f : X ⟶ X') (Y : D) (φ : F.obj X' ⟶ Y) :
    α X Y (F.map f ≫ φ) = f ≫ α X' Y φ := by
  let P : MorphismProperty W.Localization := fun X X' f =>
    ∀ (Y : D) (φ : F.obj X' ⟶ Y), α X Y (F.map f ≫ φ) = f ≫ α X' Y φ
  have : P.IsStableUnderComposition := ⟨by
      intro _ _ _ f g hf hg Y φ
      rw [F.map_comp, Category.assoc, hf, hg, Category.assoc]⟩
  have hP : P = ⊤ := Localization.Construction.morphismProperty_eq_top' (W := W) P
    (fun {_ _} f => fun Y φ => h f Y φ) (by
      intro X X' e he Y φ
      have ht := he Y (F.map e.inv ≫ φ)
      simp only [← Category.assoc, ← F.map_comp, e.hom_inv_id, F.map_id,
        Category.id_comp] at ht
      apply (cancel_epi e.hom).mp
      rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
      exact ht.symm)
  exact (show P f from hP ▸ trivial) Y φ

end SerrePositivity.DifferentialGraded
end

end LocalizationHomNaturality

/-! ## ShiftNaturalTransformation（旧 SerrePositivity/DifferentialGraded/Endomorphism/ShiftNaturalTransformation.lean） -/

/-! # 忠実な前合成による自然変換のshift整合性の検出 -/

@[expose] public section ShiftNaturalTransformation

namespace SerrePositivity.DifferentialGraded
open CategoryTheory

lemma natTransCommShift_of_faithful_precomp (S : Type*) [AddMonoid S]
    {C K T : Type*} [Category* C] [Category* K] [Category* T]
    [HasShift C S] [HasShift K S] [HasShift T S]
    (Q : C ⥤ K) [((Functor.whiskeringLeft C K T).obj Q).Faithful] [Q.CommShift S]
    {F G : K ⥤ T} [F.CommShift S] [G.CommShift S] (τ : F ⟶ G)
    (hτ : NatTrans.CommShift (Functor.whiskerLeft Q τ) S) : NatTrans.CommShift τ S where
  shift_comm s := by
    let := hτ
    apply ((Functor.whiskeringLeft C K T).obj Q).map_injective
    apply NatTrans.ext
    funext X
    rw [← cancel_epi (F.map ((Q.commShiftIso s).hom.app X))]
    have h := NatTrans.shift_app_comm (Functor.whiskerLeft Q τ) s X
    simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
      Functor.comp_obj, Category.assoc] at h
    rw [← τ.naturality_assoc] at h
    exact h

lemma quotientNatIsoLift_commShift (S : Type*) [AddMonoid S]
    {C T : Type*} [Category* C] [Category* T] [HasShift C S] [HasShift T S]
    (r : HomRel C) [r.IsCompatibleWithShift S]
    {F G : CategoryTheory.Quotient r ⥤ T} [F.CommShift S] [G.CommShift S]
    (e : CategoryTheory.Quotient.functor r ⋙ F ≅ CategoryTheory.Quotient.functor r ⋙ G)
    (he : NatTrans.CommShift e.hom S) :
    NatTrans.CommShift (CategoryTheory.Quotient.natIsoLift r e).hom S := by
  apply natTransCommShift_of_faithful_precomp S (CategoryTheory.Quotient.functor r)
  change NatTrans.CommShift e.hom S
  exact he

end SerrePositivity.DifferentialGraded

end ShiftNaturalTransformation

/-! ## GradedSplitRelations（旧 SerrePositivity/DifferentialGraded/Endomorphism/GradedSplitRelations.lean） -/

/-! # 全次数分裂の次数零Hom要素による行列恒等式 -/

@[expose] public section GradedSplitRelations
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 閉零加群射に対応する全Hom endの零次数cycle。 -/
abbrev endomorphismClosedElement {M N : ModuleCategory A D} (f : M ⟶ N) :=
  (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val

lemma endomorphismClosedElement_π {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) x).f 0 (endomorphismClosedElement A D f) =
        Cochain.ofHom ((moduleEvaluation A D x).map f) :=
  (moduleEvaluation_cochain A D x f).symm

variable {A D} {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}

lemma gradedSplit_inclusion_retraction_element (s : ModuleGradedSplit A D f g) :
    forward A (endomorphismClosedElement A D f) s.retractionElement (zero_add 0) =
      (unitElement A (ForgetEnrichment.to (Complex A) M)).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomForward_π, endomorphismClosedElement_π, s.retractionElement_π,
    yoneda_moduleUnit_π]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  apply Cochain.ext₀
  intro n
  rw [Cochain.comp_v _ _ _ n n n (add_zero n) (add_zero n)]
  simp only [Cochain.ofHom_v, Cochain.ofHoms_v, id_f]
  exact s.inclusion_retraction x n

lemma gradedSplit_section_projection_element (s : ModuleGradedSplit A D f g) :
    forward A s.sectionElement (endomorphismClosedElement A D g) (zero_add 0) =
      (unitElement A (ForgetEnrichment.to (Complex A) P)).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomForward_π, s.sectionElement_π, endomorphismClosedElement_π,
    yoneda_moduleUnit_π]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  apply Cochain.ext₀
  intro n
  rw [Cochain.comp_v _ _ _ n n n (add_zero n) (add_zero n)]
  simp only [Cochain.ofHom_v, Cochain.ofHoms_v, id_f]
  exact s.section_projection x n

lemma gradedSplit_section_retraction_element (s : ModuleGradedSplit A D f g) :
    forward A (D := RightModule A D) (x := ForgetEnrichment.to (Complex A) P)
      (y := ForgetEnrichment.to (Complex A) N) (z := ForgetEnrichment.to (Complex A) M)
      s.sectionElement s.retractionElement (zero_add 0) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomForward_π, s.sectionElement_π, s.retractionElement_π, map_zero]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  apply Cochain.ext₀
  intro n
  rw [Cochain.comp_v _ _ _ n n n (add_zero n) (add_zero n)]
  simp only [Cochain.ofHoms_v, Cochain.zero_v]
  exact s.section_retraction x n

lemma gradedSplit_decomposition_element (s : ModuleGradedSplit A D f g) :
    forward A s.retractionElement (endomorphismClosedElement A D f) (zero_add 0) +
      forward A (endomorphismClosedElement A D g) s.sectionElement (zero_add 0) =
        (unitElement A (ForgetEnrichment.to (Complex A) N)).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [map_add, moduleHomForward_π, moduleHomForward_π, s.retractionElement_π,
    s.sectionElement_π, endomorphismClosedElement_π, endomorphismClosedElement_π,
    yoneda_moduleUnit_π]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  apply Cochain.ext₀
  intro n
  rw [Cochain.add_v, Cochain.comp_v _ _ _ n n n (add_zero n) (add_zero n),
    Cochain.comp_v _ _ _ n n n (add_zero n) (add_zero n)]
  simp only [Cochain.ofHom_v, Cochain.ofHoms_v, id_f]
  exact s.decomposition x n

end SerrePositivity.DifferentialGraded
end

end GradedSplitRelations

/-! ## ZeroHomComponents（旧 SerrePositivity/DifferentialGraded/Endomorphism/ZeroHomComponents.lean） -/

/-! # 零次数Hom要素の次数付き加群射としての成分 -/

@[expose] public section ZeroHomComponents
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def zeroHomComponent {M N : RightModule A D} (a : (moduleHom A D M N).X 0)
    (x : D) (i : ℤ) : (M.obj (op x)).X i ⟶ (N.obj (op x)).X i :=
  ((moduleHomπ A D M N x).f 0 a).v i i (add_zero i)

lemma zeroHomComponent_forward {M N P : RightModule A D}
    (a : (moduleHom A D M N).X 0) (b : (moduleHom A D N P).X 0) (x : D) (i : ℤ) :
    zeroHomComponent A D (forward A (D := RightModule A D) a b (zero_add 0)) x i =
      zeroHomComponent A D a x i ≫ zeroHomComponent A D b x i := by
  unfold zeroHomComponent
  rw [moduleHomForward_π]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  exact Cochain.comp_v _ _ _ i i i (add_zero i) (add_zero i)

@[simp]
lemma zeroHomComponent_unit (M : RightModule A D) (x : D) (i : ℤ) :
    zeroHomComponent A D (unitElement A M).val x i = 𝟙 _ := by
  unfold zeroHomComponent
  rw [yoneda_moduleUnit_π]
  rfl

@[simp]
lemma zeroHomComponent_closed {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) (i : ℤ) :
    zeroHomComponent A D (endomorphismClosedElement A D f) x i =
      ((moduleEvaluation A D x).map f).f i := by
  unfold zeroHomComponent
  rw [endomorphismClosedElement_π]
  rfl

@[simp]
lemma zeroHomComponent_zero (M N : RightModule A D) (x : D) (i : ℤ) :
    zeroHomComponent A D (0 : (moduleHom A D M N).X 0) x i = 0 := by
  simp [zeroHomComponent]

@[simp]
lemma zeroHomComponent_add {M N : RightModule A D} (a b : (moduleHom A D M N).X 0)
    (x : D) (i : ℤ) :
    zeroHomComponent A D (a + b) x i = zeroHomComponent A D a x i + zeroHomComponent A D b x i := by
  simp [zeroHomComponent]

lemma zeroHomComponent_naturality {M N : RightModule A D} (a : (moduleHom A D M N).X 0)
    (x y : D) (p i j : ℤ) (hij : i + p = j) (f : GradedHom A (op x) (op y) p) :
    ((M.map (op x) (op y)).f p f).v i j hij ≫ zeroHomComponent A D a y j =
      zeroHomComponent A D a x i ≫ ((N.map (op x) (op y)).f p f).v i j hij := by
  have h := congrArg (fun c => c.v i j (by omega))
    (moduleHomElement_naturality A D 0 a (op x) (op y) p f)
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at h
  rw [Cochain.comp_v _ _ _ i j j hij (add_zero j),
    Cochain.comp_v _ _ _ i i j (add_zero i) hij] at h
  exact h

end SerrePositivity.DifferentialGraded
end

end ZeroHomComponents

/-! ## CompactHomDetectsIso（旧 SerrePositivity/DifferentialGraded/Endomorphism/CompactHomDetectsIso.lean） -/

/-! # compact対象からのHomによる主導来圏の同型判定 -/

@[expose] public section CompactHomDetectsIso
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma compactHom_shift_postcompose_injective {X Y : DerivedModuleCategory A D} (f : X ⟶ Y)
    (hInj : ∀ P : DerivedModuleCategory A D, moduleCompact A D P →
      Function.Injective (fun a : P ⟶ X => a ≫ f))
    (P : DerivedModuleCategory A D) (hP : moduleCompact A D P) :
    Function.Injective (fun a : P ⟶ X⟦(1 : ℤ)⟧ => a ≫ f⟦(1 : ℤ)⟧') := by
  let adj := (shiftEquiv' (DerivedModuleCategory A D) (-1) 1 (neg_add_cancel (1 : ℤ))).toAdjunction
  intro a b hab
  apply (adj.homEquiv P X).symm.injective
  apply hInj (P⟦(-1 : ℤ)⟧) (moduleCompact_shift A D hP (-1))
  change (adj.homEquiv P X).symm a ≫ f = (adj.homEquiv P X).symm b ≫ f
  rw [← adj.homEquiv_naturality_right_symm, ← adj.homEquiv_naturality_right_symm]
  exact congrArg ((adj.homEquiv P Y).symm) hab

/-- 既存の代表加群shiftによる零性検出を用いる。compact⇒Perfは仮定しない。 -/
lemma moduleDerived_isIso_of_compact_hom_bijective {X Y : DerivedModuleCategory A D}
    (f : X ⟶ Y)
    (hBij : ∀ P : DerivedModuleCategory A D, moduleCompact A D P →
      Function.Bijective (fun a : P ⟶ X => a ≫ f)) : IsIso f := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f g h
  have hz : IsZero Z := by
    apply (moduleCompactGenerators_detect_zero A D Z).2
    intro p
    let P := moduleCompactGenerators A D p
    have hP : moduleCompact A D P := moduleCompactGenerators_compact A D p
    have ha (a : P ⟶ Z) : a = 0 := by
      have hw : a ≫ h = 0 := by
        apply compactHom_shift_postcompose_injective A D f
          (fun Q hQ => (hBij Q hQ).1) P hP
        change (a ≫ h) ≫ f⟦(1 : ℤ)⟧' = 0 ≫ f⟦(1 : ℤ)⟧'
        have ht := comp_distTriang_mor_zero₃₁ T hT
        change h ≫ f⟦(1 : ℤ)⟧' = 0 at ht
        rw [zero_comp, Category.assoc, ht, comp_zero]
      obtain ⟨b, hb⟩ := T.coyoneda_exact₃ hT a hw
      obtain ⟨c, hc⟩ := (hBij P hP).2 b
      change c ≫ f = b at hc
      have hfg := comp_distTriang_mor_zero₁₂ T hT
      change f ≫ g = 0 at hfg
      rw [hb, ← hc, Category.assoc]
      change c ≫ f ≫ g = 0
      rw [hfg, comp_zero]
    exact ⟨fun a b => (ha a).trans (ha b).symm⟩
  exact (T.isZero₃_iff_isIso₁ hT).1 hz

end SerrePositivity.DifferentialGraded
end

end CompactHomDetectsIso

/-! ## GradedSplitOfElements（旧 SerrePositivity/DifferentialGraded/Endomorphism/GradedSplitOfElements.lean） -/

/-! # 零次数Hom要素の行列恒等式から全次数分裂を復元する -/

@[expose] public section GradedSplitOfElements
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 分裂の証拠となる零次数要素にchain map条件を課さない構成子。 -/
def moduleGradedSplitOfHomElements {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (a : (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) M)).X 0)
    (b : (moduleHom A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) N)).X 0)
    (hfa : forward A (D := RightModule A D)
      (x := ForgetEnrichment.to (Complex A) M) (y := ForgetEnrichment.to (Complex A) N)
      (z := ForgetEnrichment.to (Complex A) M) (endomorphismClosedElement A D f) a (zero_add 0) =
      (unitElement A (ForgetEnrichment.to (Complex A) M)).val)
    (hbg : forward A (D := RightModule A D)
      (x := ForgetEnrichment.to (Complex A) P) (y := ForgetEnrichment.to (Complex A) N)
      (z := ForgetEnrichment.to (Complex A) P) b (endomorphismClosedElement A D g) (zero_add 0) =
      (unitElement A (ForgetEnrichment.to (Complex A) P)).val)
    (hba : forward A (D := RightModule A D)
      (x := ForgetEnrichment.to (Complex A) P) (y := ForgetEnrichment.to (Complex A) N)
      (z := ForgetEnrichment.to (Complex A) M) b a (zero_add 0) = 0)
    (hdec : (forward A (D := RightModule A D)
      (x := ForgetEnrichment.to (Complex A) N) (y := ForgetEnrichment.to (Complex A) M)
      (z := ForgetEnrichment.to (Complex A) N) a (endomorphismClosedElement A D f) (zero_add 0) +
      forward A (D := RightModule A D)
        (x := ForgetEnrichment.to (Complex A) N) (y := ForgetEnrichment.to (Complex A) P)
        (z := ForgetEnrichment.to (Complex A) N) (endomorphismClosedElement A D g) b (zero_add 0) :
        (moduleHom A D (ForgetEnrichment.to (Complex A) N)
          (ForgetEnrichment.to (Complex A) N)).X 0) =
        (unitElement A (ForgetEnrichment.to (Complex A) N)).val)
    (hfg : f ≫ g = 0) : ModuleGradedSplit A D f g where
  retraction x n := zeroHomComponent A D a x n
  section_ x n := zeroHomComponent A D b x n
  inclusion_retraction x n := by
    have h := congrArg (fun z => zeroHomComponent A D
      (M := ForgetEnrichment.to (Complex A) M)
      (N := ForgetEnrichment.to (Complex A) M) z x n) hfa
    simp only [zeroHomComponent_forward, zeroHomComponent_closed, zeroHomComponent_unit] at h
    exact h
  section_projection x n := by
    have h := congrArg (fun z => zeroHomComponent A D
      (M := ForgetEnrichment.to (Complex A) P)
      (N := ForgetEnrichment.to (Complex A) P) z x n) hbg
    simp only [zeroHomComponent_forward, zeroHomComponent_closed, zeroHomComponent_unit] at h
    exact h
  section_retraction x n := by
    have h := congrArg (fun z => zeroHomComponent A D
      (M := ForgetEnrichment.to (Complex A) P)
      (N := ForgetEnrichment.to (Complex A) M) z x n) hba
    simp only [zeroHomComponent_forward, zeroHomComponent_zero] at h
    exact h
  inclusion_projection := hfg
  decomposition x n := by
    have h := congrArg (fun z => zeroHomComponent A D
      (M := ForgetEnrichment.to (Complex A) N)
      (N := ForgetEnrichment.to (Complex A) N) z x n) hdec
    have hadd := zeroHomComponent_add A D
      (M := ForgetEnrichment.to (Complex A) N) (N := ForgetEnrichment.to (Complex A) N)
      (forward A (D := RightModule A D) a (endomorphismClosedElement A D f) (zero_add 0))
      (forward A (D := RightModule A D) (endomorphismClosedElement A D g) b (zero_add 0)) x n
    have h' := hadd.symm.trans h
    simp only [zeroHomComponent_forward, zeroHomComponent_closed, zeroHomComponent_unit] at h'
    exact h'
  retraction_naturality x y p i j hij f := zeroHomComponent_naturality A D a x y p i j hij f
  section_naturality x y p i j hij f := (zeroHomComponent_naturality A D b x y p i j hij f).symm

end SerrePositivity.DifferentialGraded
end

end GradedSplitOfElements

/-! ## GradedSplitImage（旧 SerrePositivity/DifferentialGraded/Endomorphism/GradedSplitImage.lean） -/

/-! # 主dg加群間のdg関手は全次数分裂を保存する -/

@[expose] public section GradedSplitImage
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) (B : Type w)
  [DGCategory A D] [DGCategory A B] [Small.{u} D] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

lemma dgModuleFunctor_closedElement {M N : ModuleCategory A D} (f : M ⟶ N) :
    (F.map (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N)).f 0
        (endomorphismClosedElement A D f) =
      endomorphismClosedElement A B (F.onClosed.map f) := by
  exact (cycleFromUnit_postcomp (ForgetEnrichment.homTo (Complex A) f)
    (F.map (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N))).symm

/-- 微分と可換しない分裂要素も全Hom写像で送り、全斉次作用との可換性を保持する。 -/
def dgModuleFunctorGradedSplit {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit A D f g) :
    ModuleGradedSplit A B (F.onClosed.map f) (F.onClosed.map g) := by
  have hfa := congrArg (fun z =>
    (F.map (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) M)).f 0 z)
    (gradedSplit_inclusion_retraction_element s)
  rw [F.map_forward A, F.map_unitElement A, dgModuleFunctor_closedElement] at hfa
  have hbg := congrArg (fun z =>
    (F.map (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) P)).f 0 z)
    (gradedSplit_section_projection_element s)
  rw [F.map_forward A, F.map_unitElement A, dgModuleFunctor_closedElement] at hbg
  have hba := congrArg (fun z =>
    (F.map (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) M)).f 0 z)
    (gradedSplit_section_retraction_element s)
  rw [F.map_forward A, map_zero] at hba
  have hdec := congrArg (fun z =>
    (F.map (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) N)).f 0 z)
    (gradedSplit_decomposition_element s)
  rw [map_add, F.map_forward A, F.map_forward A, F.map_unitElement A,
    dgModuleFunctor_closedElement, dgModuleFunctor_closedElement] at hdec
  exact moduleGradedSplitOfHomElements A B (F.onClosed.map f) (F.onClosed.map g)
    ((F.map (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) M)).f 0
      s.retractionElement)
    ((F.map (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) N)).f 0
      s.sectionElement)
    hfa hbg hba hdec (by
      rw [← CategoryTheory.Functor.map_comp, s.inclusion_projection,
        CategoryTheory.Functor.map_zero])

end SerrePositivity.DifferentialGraded
end

end GradedSplitImage

/-! ## ModuleConeImage（旧 SerrePositivity/DifferentialGraded/Endomorphism/ModuleConeImage.lean） -/

/-! # 加群値dg関手による標準coneの実際の比較同型 -/

@[expose] public section ModuleConeImage
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) (B : Type w)
  [DGCategory A D] [DGCategory A B] [Small.{u} D] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

/-- coneの次数−1包含を全Hom写像で送る。 -/
def dgModuleFunctorConeInl {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A B (F.obj (ForgetEnrichment.to (Complex A) M))
      (F.obj (ForgetEnrichment.to (Complex A) (moduleCone A D f)))).X (-1) :=
  (F.map (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) (moduleCone A D f))).f (-1) (moduleConeInlElement A D f)

lemma dgModuleFunctorConeInl_d {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleHom A B (F.obj (ForgetEnrichment.to (Complex A) M))
        (F.obj (ForgetEnrichment.to (Complex A) (moduleCone A D f)))).d (-1) 0
        (dgModuleFunctorConeInl A D B F f) =
      endomorphismClosedElement A B (F.onClosed.map f ≫ F.onClosed.map (moduleConeInr A D f)) := by
  have hd := congrArg (fun k => k (moduleConeInlElement A D f))
    ((F.map (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).comm (-1) 0)
  have he := congrArg
    ((F.map (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) (moduleCone A D f))).f 0)
    (moduleConeInlElement_d A D f)
  have hc := dgModuleFunctor_closedElement A D B F (f ≫ moduleConeInr A D f)
  rw [CategoryTheory.Functor.map_comp] at hc
  exact hd.trans (he.trans hc)

/-- 閉零加群射としてのcone比較。全次数作用に関して自然。 -/
def dgModuleFunctorConeComparison {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleCone A B (F.onClosed.map f) ⟶ F.onClosed.obj (moduleCone A D f) :=
  moduleConeDescOfBoundary A B (F.onClosed.map f) (dgModuleFunctorConeInl A D B F f)
    (F.onClosed.map (moduleConeInr A D f)) (dgModuleFunctorConeInl_d A D B F f)

lemma dgModuleFunctorConeComparison_eval {M N : ModuleCategory A D} (f : M ⟶ N) (b : B) :
    (moduleEvaluation A B b).map (dgModuleFunctorConeComparison A D B F f) =
      DGFunctor.moduleConeImageComparison A D (F.comp (moduleEvaluationDG A B b)) f := by
  unfold dgModuleFunctorConeComparison
  rw [moduleConeDescOfBoundary_eval]
  rfl

instance dgModuleFunctorConeComparison_isIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    IsIso (dgModuleFunctorConeComparison A D B F f) :=
  moduleIsIso_of_evaluations A B _ (fun b => by
    rw [dgModuleFunctorConeComparison_eval]
    infer_instance)

/-- 任意の主加群値dg関手は主加群coneを、実際の加群同型まで保つ。 -/
def dgModuleFunctorConeIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleCone A B (F.onClosed.map f) ≅ F.onClosed.obj (moduleCone A D f) :=
  asIso (dgModuleFunctorConeComparison A D B F f)

lemma dgModuleFunctorConeComparison_inr {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeInr A B (F.onClosed.map f) ≫ dgModuleFunctorConeComparison A D B F f =
      F.onClosed.map (moduleConeInr A D f) :=
  moduleConeDescOfBoundary_inr A B _ _ _ _

end SerrePositivity.DifferentialGraded
end

end ModuleConeImage

/-! ## ModuleShiftImage（旧 SerrePositivity/DifferentialGraded/Endomorphism/ModuleShiftImage.lean） -/

/-! # 加群値dg関手のshift比較同型を全次数自然な加群同型に組み立てる -/

@[expose] public section ModuleShiftImage
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type w) [DGCategory A B] [Small.{u} B]

lemma moduleShiftRepresentation_naturality (s : ℤ) {U V : RightModule A B}
    (a : (moduleHom A B U V).X s)
    (c : ∀ x : Bᵒᵖ, U.obj x ⟶ (shiftModule s V).obj x)
    (hc : ∀ (x : Bᵒᵖ) (i : ℤ), (c x).f i =
      ((moduleHomπ A B U V x.unop).f s a).v i (i + s) rfl) :
    ∀ x y, U.map x y ≫ homPostcompose (U.obj x) (c y) =
      (shiftModule s V).map x y ≫ homPrecompose (c x) ((shiftModule s V).obj y) := by
  apply closedFamily_of_action A c
  intro x y p r n hn f v
  change (c y).f n (((U.map x y).f p f).v r n hn v) =
    (((shiftModule s V).map x y).f p f).v r n hn ((c x).f r v)
  rw [hc, hc, shiftModule_map_v]
  have h := congrArg (fun z => z.v r (n + s) (by omega))
    (moduleHomElement_naturality A B s a x y p f)
  rw [Cochain.comp_v _ _ _ r n (n + s) hn rfl, Cochain.units_smul_v,
    Cochain.comp_v _ _ _ r (r + s) (n + s) rfl (by omega)] at h
  exact congrArg (fun k => k v) h

variable (D : Type v) [DGCategory A D] [Small.{u} D]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

lemma dgModuleFunctorShift_naturality (s : ℤ) (M : RightModule A D) :
    ∀ x y, (F.obj (shiftModule s M)).map x y ≫
        homPostcompose ((F.obj (shiftModule s M)).obj x)
          (DGFunctor.moduleShiftImageIso A D (F.comp (moduleEvaluationDG A B y.unop)) s M).hom =
      (shiftModule s (F.obj M)).map x y ≫
        homPrecompose
          (DGFunctor.moduleShiftImageIso A D (F.comp (moduleEvaluationDG A B x.unop)) s M).hom
          ((shiftModule s (F.obj M)).obj y) := by
  apply moduleShiftRepresentation_naturality A B s
    ((F.map (shiftModule s M) M).f s (moduleShiftOutElement A D s M))
  intro x i
  exact DGFunctor.moduleShiftImageComparison_f A D (F.comp (moduleEvaluationDG A B x.unop)) s M i

/-- 評価成分のshift同型を、主加群の全次数自然な同型へ組み立てる。 -/
def dgModuleFunctorShiftIso (s : ℤ) (M : RightModule A D) :
    ForgetEnrichment.of (Complex A) (F.obj (shiftModule s M)) ≅
      ForgetEnrichment.of (Complex A) (shiftModule s (F.obj M)) :=
  moduleIsoMk A B
    (fun x => DGFunctor.moduleShiftImageIso A D (F.comp (moduleEvaluationDG A B x.unop)) s M)
    (dgModuleFunctorShift_naturality A B D F s M)

lemma dgModuleFunctorShiftIso_hom_eval (s : ℤ) (M : RightModule A D) (b : B) :
    (moduleEvaluation A B b).map (dgModuleFunctorShiftIso A B D F s M).hom =
      (DGFunctor.moduleShiftImageIso A D (F.comp (moduleEvaluationDG A B b)) s M).hom :=
  moduleIsoMk_hom_eval A B _ _ b

end SerrePositivity.DifferentialGraded
end

end ModuleShiftImage
