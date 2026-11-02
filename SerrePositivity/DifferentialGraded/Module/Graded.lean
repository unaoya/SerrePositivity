module

public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Module.ActionLimits
public import SerrePositivity.DifferentialGraded.Complexes.Cone
public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Module.Graded

## 概要
12 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## Isomorphism（旧 SerrePositivity/DifferentialGraded/Module/Isomorphism.lean） -/

/-! # 全次数自然な複体同型族からの加群同型 -/

@[expose] public section Isomorphism
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 全次数自然な同型族の逆も全次数自然。 -/
lemma moduleIsoFamily_inv_naturality {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ≅ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y).hom =
      N.map x y ≫ homPrecompose (a x).hom (N.obj y)) (x y : Dᵒᵖ) :
    N.map x y ≫ homPostcompose (N.obj x) (a y).inv =
      M.map x y ≫ homPrecompose (a x).inv (M.obj y) := by
  apply closedFamily_of_action A (M := N) (N := M) (fun x => (a x).inv)
  intro x y p r n hn f v
  have hh := closedFamily_action A (fun x => (a x).hom) h x y p r n hn f ((a x).inv.f r v)
  have hi := congrArg (fun t => (a y).inv.f n t) hh
  simp only [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
    Iso.hom_inv_id, Iso.inv_hom_id, HomologicalComplex.id_f, ModuleCat.id_apply] at hi
  exact hi.symm

variable (D) [Small.{u} D]

/-- 全次数自然な同型族を主 Hom end の閉零加群同型へ持ち上げる。 -/
def moduleIsoMk {M N : RightModule A D} (a : ∀ x : Dᵒᵖ, M.obj x ≅ N.obj x)
    (h : ∀ x y : Dᵒᵖ, M.map x y ≫ homPostcompose (M.obj x) (a y).hom =
      N.map x y ≫ homPrecompose (a x).hom (N.obj y)) :
    ForgetEnrichment.of (Complex A) M ≅ ForgetEnrichment.of (Complex A) N where
  hom := moduleMorphismMk A D (fun x => (a x).hom) h
  inv := moduleMorphismMk A D (fun x => (a x).inv) (moduleIsoFamily_inv_naturality A a h)
  hom_inv_id := by
    apply moduleMorphism_ext
    intro x
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      moduleMorphismMk_eval, moduleMorphismMk_eval]
    exact (a (op x)).hom_inv_id
  inv_hom_id := by
    apply moduleMorphism_ext
    intro x
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
      moduleMorphismMk_eval, moduleMorphismMk_eval]
    exact (a (op x)).inv_hom_id

@[simp] lemma moduleIsoMk_hom_eval {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ≅ N.obj x) (h) (x : D) :
    (moduleEvaluation A D x).map (moduleIsoMk A D a h).hom = (a (op x)).hom :=
  moduleMorphismMk_eval A D _ _ x

@[simp] lemma moduleIsoMk_inv_eval {M N : RightModule A D}
    (a : ∀ x : Dᵒᵖ, M.obj x ≅ N.obj x) (h) (x : D) :
    (moduleEvaluation A D x).map (moduleIsoMk A D a h).inv = (a (op x)).inv :=
  moduleMorphismMk_eval A D _ _ x
end SerrePositivity.DifferentialGraded
end

end Isomorphism

/-! ## GradedSplit（旧 SerrePositivity/DifferentialGraded/Module/GradedSplit.lean） -/

/-! # 全次数作用に関して分裂するdg加群の拡大

section/retractionにchain map条件は課さない。微分を忘れた次数付き加群での分裂を記録する。
主dg加群モデルは変更しない。
-/

@[expose] public section GradedSplit
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 主加群の全整数次数の作用をModuleCatの射として読む。 -/
abbrev moduleActionComponent (M : ModuleCategory A D) (x y : D)
    (p i j : ℤ) (hij : i + p = j) (a : GradedHom A (op x) (op y) p) :=
  (((ForgetEnrichment.to (Complex A) M).map (op x) (op y)).f p a).v i j hij

/-- dg加群拡大の、全斉次作用と可換する次数付き分裂。 -/
structure ModuleGradedSplit {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) where
  retraction (x : D) (n : ℤ) : ((moduleEvaluation A D x).obj N).X n ⟶
    ((moduleEvaluation A D x).obj M).X n
  section_ (x : D) (n : ℤ) : ((moduleEvaluation A D x).obj P).X n ⟶
    ((moduleEvaluation A D x).obj N).X n
  inclusion_retraction (x : D) (n : ℤ) :
    ((moduleEvaluation A D x).map f).f n ≫ retraction x n = 𝟙 _
  section_projection (x : D) (n : ℤ) :
    section_ x n ≫ ((moduleEvaluation A D x).map g).f n = 𝟙 _
  section_retraction (x : D) (n : ℤ) : section_ x n ≫ retraction x n = 0
  inclusion_projection : f ≫ g = 0
  decomposition (x : D) (n : ℤ) :
    retraction x n ≫ ((moduleEvaluation A D x).map f).f n +
      ((moduleEvaluation A D x).map g).f n ≫ section_ x n = 𝟙 _
  retraction_naturality (x y : D) (p i j : ℤ) (hij : i + p = j)
      (a : GradedHom A (op x) (op y) p) :
    moduleActionComponent A D N x y p i j hij a ≫ retraction y j =
      retraction x i ≫ moduleActionComponent A D M x y p i j hij a
  section_naturality (x y : D) (p i j : ℤ) (hij : i + p = j)
      (a : GradedHom A (op x) (op y) p) :
    section_ x i ≫ moduleActionComponent A D N x y p i j hij a =
      moduleActionComponent A D P x y p i j hij a ≫ section_ y j

namespace ModuleGradedSplit
variable {A D} {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}

lemma degreewiseMono (s : ModuleGradedSplit A D f g) (x : D) (n : ℤ) :
    Mono (((moduleEvaluation A D x).map f).f n) := by
  let : IsSplitMono (((moduleEvaluation A D x).map f).f n) :=
    ⟨⟨{ retraction := s.retraction x n, id := s.inclusion_retraction x n }⟩⟩
  infer_instance

lemma degreewiseEpi (s : ModuleGradedSplit A D f g) (x : D) (n : ℤ) :
    Epi (((moduleEvaluation A D x).map g).f n) := by
  let : IsSplitEpi (((moduleEvaluation A D x).map g).f n) :=
    ⟨⟨{ section_ := s.section_ x n, id := s.section_projection x n }⟩⟩
  infer_instance

lemma mono (s : ModuleGradedSplit A D f g) : Mono f where
  right_cancellation b c h := by
    apply moduleMorphism_ext
    intro x
    apply HomologicalComplex.Hom.ext
    funext n
    let : Mono (((moduleEvaluation A D x).map f).f n) := s.degreewiseMono x n
    apply (cancel_mono (((moduleEvaluation A D x).map f).f n)).1
    have he := congrArg (fun a => ((moduleEvaluation A D x).map a).f n) h
    simpa only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] using he

lemma epi (s : ModuleGradedSplit A D f g) : Epi g where
  left_cancellation b c h := by
    apply moduleMorphism_ext
    intro x
    apply HomologicalComplex.Hom.ext
    funext n
    let : Epi (((moduleEvaluation A D x).map g).f n) := s.degreewiseEpi x n
    apply (cancel_epi (((moduleEvaluation A D x).map g).f n)).1
    have he := congrArg (fun a => ((moduleEvaluation A D x).map a).f n) h
    simpa only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] using he

def evaluationShortComplex (s : ModuleGradedSplit A D f g) (x : D) (n : ℤ) :
    ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk (((moduleEvaluation A D x).map f).f n)
    (((moduleEvaluation A D x).map g).f n) (by
      have h := congrArg (fun a => ((moduleEvaluation A D x).map a).f n) s.inclusion_projection
      rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
        CategoryTheory.Functor.map_zero, HomologicalComplex.zero_f] at h
      exact h)

lemma evaluationShortExact (s : ModuleGradedSplit A D f g) (x : D) (n : ℤ) :
    (s.evaluationShortComplex x n).ShortExact where
  exact := by
    apply (ShortComplex.moduleCat_exact_iff _).2
    intro z hz
    refine ⟨s.retraction x n z, ?_⟩
    have h := congrArg (fun a => a z) (s.decomposition x n)
    change (((moduleEvaluation A D x).map f).f n) (s.retraction x n z) +
      s.section_ x n ((((moduleEvaluation A D x).map g).f n) z) = z at h
    change (((moduleEvaluation A D x).map g).f n) z = 0 at hz
    rw [hz, map_zero, add_zero] at h
    exact h
  mono_f := s.degreewiseMono x n
  epi_g := s.degreewiseEpi x n

def evaluationCokernel (s : ModuleGradedSplit A D f g) (x : D) :
    IsColimit (CokernelCofork.ofπ (f := (moduleEvaluation A D x).map f)
      ((moduleEvaluation A D x).map g)
      (by rw [← CategoryTheory.Functor.map_comp, s.inclusion_projection,
        CategoryTheory.Functor.map_zero])) := by
  apply HomologicalComplex.isColimitOfEval
  intro n
  refine (isColimitMapCoconeCoforkEquiv'
    (f := (moduleEvaluation A D x).map f) (h := (moduleEvaluation A D x).map g)
    (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n) _).symm ?_
  let : Epi (s.evaluationShortComplex x n).g := (s.evaluationShortExact x n).epi_g
  exact (s.evaluationShortExact x n).exact.gIsCokernel

end ModuleGradedSplit

end SerrePositivity.DifferentialGraded
end

end GradedSplit

/-! ## GradedSplitElements（旧 SerrePositivity/DifferentialGraded/Module/GradedSplitElements.lean） -/

/-! # 次数付き自然変換と分裂の主Hom end要素

微分との可換性を要求しない次数零要素としてretractionとsectionを扱う。
-/

@[expose] public section GradedSplitElements
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleGradedNaturalElement {M N : ModuleCategory A D}
    (a : ∀ x : D, ∀ n : ℤ,
      ((moduleEvaluation A D x).obj M).X n ⟶ ((moduleEvaluation A D x).obj N).X n)
    (ha : ∀ (x y : D) (p i j : ℤ) (hij : i + p = j)
      (f : GradedHom A (op x) (op y) p),
      moduleActionComponent A D M x y p i j hij f ≫ a y j =
        a x i ≫ moduleActionComponent A D N x y p i j hij f) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)).X 0 :=
  moduleHomElementMk A D (M := ForgetEnrichment.to (Complex A) M)
    (N := ForgetEnrichment.to (Complex A) N) 0 (fun x => Cochain.ofHoms (a x.unop)) (by
    intro x y p f
    simp only [zero_mul, Int.negOnePow_zero, one_smul]
    apply Cochain.ext
    intro i j hij
    rw [Cochain.comp_v _ _ _ i j j (by omega) (add_zero j),
      Cochain.comp_v _ _ _ i i j (add_zero i) (by omega)]
    simp only [Cochain.ofHoms_v]
    exact ha x.unop y.unop p i j (by omega) f)

lemma moduleGradedNaturalElement_π {M N : ModuleCategory A D} (a) (ha) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N) x).f 0 (moduleGradedNaturalElement A D a ha) =
        Cochain.ofHoms (a x) := moduleHomElementMk_π A D 0 _ _ x

namespace ModuleGradedSplit
variable {A D} {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}

def retractionElement (s : ModuleGradedSplit A D f g) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) M)).X 0 :=
  moduleGradedNaturalElement A D s.retraction s.retraction_naturality

def sectionElement (s : ModuleGradedSplit A D f g) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) N)).X 0 :=
  moduleGradedNaturalElement A D s.section_
    (fun x y p i j hij a => (s.section_naturality x y p i j hij a).symm)

lemma retractionElement_π (s : ModuleGradedSplit A D f g) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) M) x).f 0 s.retractionElement =
        Cochain.ofHoms (s.retraction x) := moduleGradedNaturalElement_π A D _ _ x

lemma sectionElement_π (s : ModuleGradedSplit A D f g) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) N) x).f 0 s.sectionElement =
        Cochain.ofHoms (s.section_ x) := moduleGradedNaturalElement_π A D _ _ x

/-- 包含への前合成を次数ごとに分裂する。chain mapとは主張しない。 -/
def homRestrictionSection (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (q : ℤ) (z : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) T)).X q) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) T)).X q :=
  forward A (x := ForgetEnrichment.to (Complex A) N)
    (y := ForgetEnrichment.to (Complex A) M) (z := ForgetEnrichment.to (Complex A) T)
    s.retractionElement z (zero_add q)

lemma homRestrictionSection_π (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (q : ℤ) (z : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) T)).X q) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) T) x).f q (s.homRestrictionSection T q z) =
      (Cochain.ofHoms (s.retraction x)).comp
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
          (ForgetEnrichment.to (Complex A) T) x).f q z) (zero_add q) := by
  rw [homRestrictionSection, moduleHomForward_π, zero_mul, Int.negOnePow_zero,
    one_smul, s.retractionElement_π]

lemma homRestriction_section (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (q : ℤ) (z : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) T)).X q) :
    (eHomWhiskerRight (Complex A) f T).f q (s.homRestrictionSection T q z) = z := by
  apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) M)
    (N := ForgetEnrichment.to (Complex A) T)
  intro x
  rw [moduleHomWhiskerRight_apply_π A D f q _ x, s.homRestrictionSection_π]
  apply Cochain.ext
  intro i j hij
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.ofHoms_v]
  rw [← Category.assoc, s.inclusion_retraction, Category.id_comp]

lemma homRestriction_surjective (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (q : ℤ) : Function.Surjective ((eHomWhiskerRight (Complex A) f T).f q) :=
  fun z => ⟨s.homRestrictionSection T q z, s.homRestriction_section T q z⟩

end ModuleGradedSplit
end SerrePositivity.DifferentialGraded
end

end GradedSplitElements

/-! ## GradedSplitHomExact（旧 SerrePositivity/DifferentialGraded/Module/GradedSplitHomExact.lean） -/

/-! # 次数付き分裂に対するHom endのkernelの同定 -/

@[expose] public section GradedSplitHomExact
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] [Small.{u} D]
namespace ModuleGradedSplit
variable {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}

/-- 商のsectionへの前合成。Hom複体のchain mapとは要求しない。 -/
def homKernelRetraction (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (q : ℤ) (z : (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) T)).X q) :
    (moduleHom A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) T)).X q :=
  forward A (x := ForgetEnrichment.to (Complex A) P)
    (y := ForgetEnrichment.to (Complex A) N) (z := ForgetEnrichment.to (Complex A) T)
    s.sectionElement z (zero_add q)

lemma homKernelRetraction_π (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (q : ℤ) (z : (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) T)).X q) (x : D) :
    (moduleHomπ A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) T) x).f q (s.homKernelRetraction T q z) =
      (Cochain.ofHoms (s.section_ x)).comp
        ((moduleHomπ A D (ForgetEnrichment.to (Complex A) N)
          (ForgetEnrichment.to (Complex A) T) x).f q z) (zero_add q) := by
  rw [homKernelRetraction, moduleHomForward_π, zero_mul, Int.negOnePow_zero,
    one_smul, s.sectionElement_π]

lemma homKernel_retraction (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (q : ℤ) (z : (moduleHom A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) T)).X q) :
    s.homKernelRetraction T q ((eHomWhiskerRight (Complex A) g T).f q z) = z := by
  apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) P)
    (N := ForgetEnrichment.to (Complex A) T)
  intro x
  rw [s.homKernelRetraction_π, moduleHomWhiskerRight_apply_π A D g q z x]
  apply Cochain.ext
  intro i j hij
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.ofHoms_v]
  rw [← Category.assoc, s.section_projection, Category.id_comp]

lemma homKernel_injective (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (q : ℤ) : Function.Injective ((eHomWhiskerRight (Complex A) g T).f q) := by
  intro z w h
  have he := congrArg (s.homKernelRetraction T q) h
  simpa only [s.homKernel_retraction] using he

lemma homKernel_of_restriction_zero (s : ModuleGradedSplit A D f g)
    (T : ModuleCategory A D) (q : ℤ)
    (z : (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) T)).X q)
    (hz : (eHomWhiskerRight (Complex A) f T).f q z = 0) :
    (eHomWhiskerRight (Complex A) g T).f q (s.homKernelRetraction T q z) = z := by
  apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) N)
    (N := ForgetEnrichment.to (Complex A) T)
  intro x
  rw [moduleHomWhiskerRight_apply_π A D g q _ x, s.homKernelRetraction_π]
  apply Cochain.ext
  intro i j hij
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.ofHoms_v]
  have hx := congrArg (fun a => (moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) T) x).f q a) hz
  rw [moduleHomWhiskerRight_apply_π A D f q z x, map_zero] at hx
  have hxi := congrArg (fun a => a.v i j hij) hx
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v] at hxi
  have hd := congrArg (fun a => a ≫
    ((moduleHomπ A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) T) x).f q z).v i j hij) (s.decomposition x i)
  rw [Preadditive.add_comp, Category.id_comp, Category.assoc, hxi,
    comp_zero, zero_add] at hd
  exact (Category.assoc _ _ _).symm.trans hd

lemma homKernel_restriction_zero (s : ModuleGradedSplit A D f g)
    (T : ModuleCategory A D) (q : ℤ)
    (z : (moduleHom A D (ForgetEnrichment.to (Complex A) P)
      (ForgetEnrichment.to (Complex A) T)).X q) :
    (eHomWhiskerRight (Complex A) f T).f q
      ((eHomWhiskerRight (Complex A) g T).f q z) = 0 := by
  apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) M)
    (N := ForgetEnrichment.to (Complex A) T)
  intro x
  rw [moduleHomWhiskerRight_apply_π A D f q _ x,
    moduleHomWhiskerRight_apply_π A D g q z x, map_zero]
  apply Cochain.ext
  intro i j hij
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v]
  have hfg := congrArg (fun a => ((moduleEvaluation A D x).map a).f i)
    s.inclusion_projection
  simp only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
    CategoryTheory.Functor.map_zero, HomologicalComplex.zero_f] at hfg
  rw [← Category.assoc, hfg, zero_comp]

/-- Homは全次数分裂する拡大を複体の短複体へ送る。 -/
def homShortComplex (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D) :
    ShortComplex (Complex A) :=
  ShortComplex.mk (eHomWhiskerRight (Complex A) g T)
    (eHomWhiskerRight (Complex A) f T) (by
      apply HomologicalComplex.Hom.ext
      funext q
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact s.homKernel_restriction_zero T q z)

lemma homShortComplex_degreewise_shortExact (s : ModuleGradedSplit A D f g)
    (T : ModuleCategory A D) (q : ℤ) :
    ((s.homShortComplex T).map
      (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) q)).ShortExact where
  exact := by
    apply (ShortComplex.moduleCat_exact_iff _).2
    intro z hz
    exact ⟨s.homKernelRetraction T q z, s.homKernel_of_restriction_zero T q z hz⟩
  mono_f := (ModuleCat.mono_iff_injective _).2 (s.homKernel_injective T q)
  epi_g := (ModuleCat.epi_iff_surjective _).2 (s.homRestriction_surjective T q)

lemma homShortComplex_shortExact (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D) :
    (s.homShortComplex T).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (s.homShortComplex_degreewise_shortExact T)

end ModuleGradedSplit
end SerrePositivity.DifferentialGraded
end

end GradedSplitHomExact

/-! ## GradedSplitCokernel（旧 SerrePositivity/DifferentialGraded/Module/GradedSplitCokernel.lean） -/

/-! # 次数付き分裂拡大の商の普遍性

各評価のcokernelを全dg自然な加群のcokernelへ接続する。
-/

@[expose] public section GradedSplitCokernel
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N P T : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}

/-- 各評価複体のcokernelからの延長。 -/
def moduleGradedSplitDescFamily (s : ModuleGradedSplit A D f g) (q : N ⟶ T)
    (h : f ≫ q = 0) (x : Dᵒᵖ) :
    (moduleEvaluation A D x.unop).obj P ⟶ (moduleEvaluation A D x.unop).obj T :=
  (s.evaluationCokernel x.unop).desc (CokernelCofork.ofπ
    ((moduleEvaluation A D x.unop).map q) (by
      rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_zero]))

lemma moduleGradedSplitDescFamily_fac (s : ModuleGradedSplit A D f g) (q : N ⟶ T)
    (h : f ≫ q = 0) (x : Dᵒᵖ) :
    (moduleEvaluation A D x.unop).map g ≫ moduleGradedSplitDescFamily A D s q h x =
      (moduleEvaluation A D x.unop).map q :=
  Cofork.IsColimit.π_desc (s.evaluationCokernel x.unop)

lemma moduleGradedSplitDescFamily_naturality (s : ModuleGradedSplit A D f g) (q : N ⟶ T)
    (h : f ≫ q = 0) (x y : Dᵒᵖ) :
    (ForgetEnrichment.to (Complex A) P).map x y ≫
      homPostcompose ((ForgetEnrichment.to (Complex A) P).obj x)
        (moduleGradedSplitDescFamily A D s q h y) =
    (ForgetEnrichment.to (Complex A) T).map x y ≫
      homPrecompose (moduleGradedSplitDescFamily A D s q h x)
        ((ForgetEnrichment.to (Complex A) T).obj y) := by
  apply closedFamily_of_action A (moduleGradedSplitDescFamily A D s q h)
  intro x y p i j hij a v
  obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective _).1 (s.degreewiseEpi x.unop i) v
  have hg := closedFamily_action A
    (closedTransApp A (moduleClosedHomEquiv A D N P g))
    (closedTransApp_naturality A (moduleClosedHomEquiv A D N P g)) x y p i j hij a w
  have hq := closedFamily_action A
    (closedTransApp A (moduleClosedHomEquiv A D N T q))
    (closedTransApp_naturality A (moduleClosedHomEquiv A D N T q)) x y p i j hij a w
  have hx := congrArg (fun b => b.f i w) (moduleGradedSplitDescFamily_fac A D s q h x)
  have hy := congrArg (fun b => b.f j
    (moduleAction A (ForgetEnrichment.to (Complex A) N) a w hij))
    (moduleGradedSplitDescFamily_fac A D s q h y)
  change (moduleGradedSplitDescFamily A D s q h x).f i
    (((moduleEvaluation A D x.unop).map g).f i w) =
      ((moduleEvaluation A D x.unop).map q).f i w at hx
  change (moduleGradedSplitDescFamily A D s q h y).f j
    (((moduleEvaluation A D y.unop).map g).f j
      (moduleAction A (ForgetEnrichment.to (Complex A) N) a w hij)) =
    ((moduleEvaluation A D y.unop).map q).f j
      (moduleAction A (ForgetEnrichment.to (Complex A) N) a w hij) at hy
  rw [← hw]
  exact (congrArg ((moduleGradedSplitDescFamily A D s q h y).f j) hg.symm).trans
    (hy.trans (hq.trans (congrArg (fun z =>
      moduleAction A (ForgetEnrichment.to (Complex A) T) a z hij) hx.symm)))

def moduleGradedSplitDesc (s : ModuleGradedSplit A D f g) (q : N ⟶ T) (h : f ≫ q = 0) :
    P ⟶ T :=
  moduleMorphismMk A D (M := ForgetEnrichment.to (Complex A) P)
    (N := ForgetEnrichment.to (Complex A) T) (moduleGradedSplitDescFamily A D s q h)
    (moduleGradedSplitDescFamily_naturality A D s q h)

@[reassoc] lemma moduleGradedSplitDesc_fac (s : ModuleGradedSplit A D f g)
    (q : N ⟶ T) (h : f ≫ q = 0) : g ≫ moduleGradedSplitDesc A D s q h = q := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp]
  unfold moduleGradedSplitDesc
  rw [moduleMorphismMk_eval]
  exact moduleGradedSplitDescFamily_fac A D s q h (op x)

/-- 次数付き分裂拡大の第三対象は主dg加群圏での真のcokernel。 -/
def moduleGradedSplitCokernel (s : ModuleGradedSplit A D f g) :
    IsColimit (CokernelCofork.ofπ g s.inclusion_projection) :=
  CokernelCofork.IsColimit.ofπ g s.inclusion_projection
    (fun q h => moduleGradedSplitDesc A D s q h)
    (fun q h => moduleGradedSplitDesc_fac A D s q h)
    (by
      intro T q h b hb
      let : Epi g := s.epi
      apply (cancel_epi g).1
      exact hb.trans (moduleGradedSplitDesc_fac A D s q h).symm)

end SerrePositivity.DifferentialGraded
end

end GradedSplitCokernel

/-! ## YonedaFunctor（旧 SerrePositivity/DifferentialGraded/Module/YonedaFunctor.lean） -/

/-! # 全Hom endに値を持つdg Yoneda関手 -/

@[expose] public section YonedaFunctor
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 代表対象のHomを代表加群間の全Hom endへ送る。 -/
def yonedaHom (x y : D) :
    (x ⟶[Complex A] y) ⟶ moduleHom A D (representable A x) (representable A y) :=
  (dgYonedaIso A x (representable A y)).inv

@[reassoc]
lemma yonedaHom_π (x y b : D) :
    yonedaHom A D x y ≫ moduleHomπ A D (representable A x) (representable A y) b =
      yonedaExtensionApp A x (representable A y) (𝟙 _) (op b) :=
  moduleHomEquiv_symm_π A D _ _ _ (yonedaExtension A x (representable A y) (𝟙 _)) b

lemma yonedaHom_element (x y b : D) {p r n : ℤ} (f : GradedHom A x y p)
    (h : GradedHom A b x r) (hn : r + p = n) :
    (((moduleHomπ A D (representable A x) (representable A y) b).f p
      ((yonedaHom A D x y).f p f)).v r n hn) h =
    (p * r).negOnePow • forward A h f hn := by
  have hp := congrArg (fun t => t.f p f) (yonedaHom_π A D x y b)
  change (moduleHomπ A D (representable A x) (representable A y) b).f p
    ((yonedaHom A D x y).f p f) = _ at hp
  rw [hp]
  have he := yonedaExtensionApp_apply A x (representable A y) (𝟙 _) (op b) p r n hn f h
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply] at he
  change (((yonedaExtensionApp A x (representable A y) (𝟙 _) (op b)).f p f).v r n hn) h =
    (p * r).negOnePow • forward A (D := D) (x := b) (y := x) (z := y) h f hn at he
  exact he

/-- 代表加群からのHomの斉次要素は単位元での評価で判定できる。 -/
lemma yoneda_element_ext (x : D) (M : RightModule A D) {q : ℤ}
    {t s : (moduleHom A D (representable A x) M).X q}
    (h : (((moduleHomπ A D (representable A x) M x).f q t).v 0 q (zero_add q))
        (unitElement A x).val =
      (((moduleHomπ A D (representable A x) M x).f q s).v 0 q (zero_add q))
        (unitElement A x).val) : t = s := by
  apply (ModuleCat.mono_iff_injective ((dgYonedaIso A x M).hom.f q)).mp inferInstance
  change (yonedaEvaluateFamily A x M
      (fun y => moduleHomπ A D (representable A x) M y.unop)).f q t =
    (yonedaEvaluateFamily A x M
      (fun y => moduleHomπ A D (representable A x) M y.unop)).f q s
  rw [yonedaEvaluateFamily_apply, yonedaEvaluateFamily_apply]
  exact h

lemma yoneda_moduleUnit_π (M : RightModule A D) (b : D) :
    (moduleHomπ A D M M b).f 0 (unitElement A M).val = Cochain.ofHom (𝟙 (M.obj (op b))) := by
  have h := congrArg (fun f => (cycleFromUnit _ f).val) (moduleIdentity_π A D M b)
  rw [cycleFromUnit_postcomp, identity, cycleFromUnit_unitFromCycle] at h
  exact h

lemma yonedaHom_unit (x : D) :
    (yonedaHom A D x x).f 0 (unitElement A x).val = (unitElement A (representable A x)).val := by
  apply yoneda_element_ext A D x (representable A x)
  rw [yonedaHom_element, yoneda_moduleUnit_π, Cochain.ofHom_v]
  simp only [mul_zero, Int.negOnePow_zero, one_smul, unit_forward,
    HomologicalComplex.id_f, ModuleCat.id_apply]

lemma yonedaHom_forward {x y z : D} {p q k : ℤ} (f : GradedHom A x y p)
    (g : GradedHom A y z q) (hk : p + q = k) :
    (yonedaHom A D x z).f k (forward A f g hk) =
      forward A (D := RightModule A D) (x := representable A x) (y := representable A y)
        (z := representable A z) ((yonedaHom A D x y).f p f) ((yonedaHom A D y z).f q g) hk := by
  apply yoneda_element_ext A D x (representable A z)
  rw [yonedaHom_element, moduleHomForward_π, Cochain.units_smul_v,
    Cochain.comp_v _ _ hk 0 p k (zero_add p) hk]
  change (k * 0).negOnePow • forward A (unitElement A x).val (forward A f g hk)
      (zero_add k) =
    (p * q).negOnePow •
      (((moduleHomπ A D (representable A y) (representable A z) x).f q
        ((yonedaHom A D y z).f q g)).v p k hk
          ((((moduleHomπ A D (representable A x) (representable A y) x).f p
            ((yonedaHom A D x y).f p f)).v 0 p (zero_add p)) (unitElement A x).val))
  rw [yonedaHom_element]
  simp only [mul_zero, Int.negOnePow_zero, one_smul, forward_unit]
  rw [yonedaHom_element, mul_comm q p, smul_smul, Int.units_mul_self, one_smul]
  simp only [mul_zero, Int.negOnePow_zero, one_smul, forward_unit]

/-- Mathlib豊穣関手としてのdg Yoneda。 -/
def dgYoneda : DGFunctor A D (RightModule A D) :=
  DGFunctor.ofHomMaps A (representable A) (yonedaHom A D)
    (yonedaHom_unit A D) (fun _ _ _ _ _ _ hk f g => yonedaHom_forward A D f g hk)

end SerrePositivity.DifferentialGraded
end

end YonedaFunctor

/-! ## YonedaClosedPreimage（旧 SerrePositivity/DifferentialGraded/Module/YonedaClosedPreimage.lean） -/

/-!
概要：代表加群間の実閉射の Yoneda 逆像を、元の全 Hom 同型で指定する。
方針：閉射を単位複体からの射として読み、Yoneda 評価と合成する。
規約：像は元の同じ加群閉射へ厳密に戻り、対象輸送を追加しない。
使われ方：c′ の行有限行列の元の dg 圏における係数を固定する。
-/

@[expose] public section YonedaClosedPreimage
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

def dgYonedaClosedPreimage {x y : D}
    (f : ForgetEnrichment.of (Complex R) (representable R x) ⟶
      ForgetEnrichment.of (Complex R) (representable R y)) :
    ForgetEnrichment.of (Complex R) x ⟶ ForgetEnrichment.of (Complex R) y :=
  ForgetEnrichment.homOf (Complex R)
    (ForgetEnrichment.homTo (Complex R) f ≫ (dgYonedaIso R x (representable R y)).hom)

lemma dgYonedaClosedPreimage_map {x y : D}
    (f : ForgetEnrichment.of (Complex R) (representable R x) ⟶
      ForgetEnrichment.of (Complex R) (representable R y)) :
    (dgYoneda R D).onClosed.map (dgYonedaClosedPreimage R D f) = f := by
  change (ForgetEnrichment.homTo (Complex R) f ≫ (dgYonedaIso R x (representable R y)).hom) ≫
    (dgYonedaIso R x (representable R y)).inv = ForgetEnrichment.homTo (Complex R) f
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.DifferentialGraded
end

end YonedaClosedPreimage

/-! ## LeftMorphisms（旧 SerrePositivity/DifferentialGraded/Module/LeftMorphisms.lean） -/

/-! # 左dg加群の閉零射と全次数作用の可換性 -/

@[expose] public section LeftMorphisms
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左閉零射を二重opposite表示の全次数自然変換として読む。 -/
def leftModuleClosedHomEquiv (M N : LeftModuleCategory A D) :
    (M ⟶ N) ≃ ModuleParamTrans A Dᵒᵖ (𝟙_ (Complex A))
      (ForgetEnrichment.to (Complex A) M).toRightOpposite
      (ForgetEnrichment.to (Complex A) N).toRightOpposite :=
  moduleHomEquiv A Dᵒᵖ _ _ _

lemma leftModuleEvaluation_map (x : D) {M N : LeftModuleCategory A D} (f : M ⟶ N) :
    (leftModuleEvaluation A D x).map f =
      closedTransApp A (leftModuleClosedHomEquiv A D M N f) (op (op x)) := rfl

/-- 左加群の実際の射は、任意次数のHomに対するtensor作用と可換。 -/
lemma leftModuleMorphism_action_chain {M N : LeftModuleCategory A D} (f : M ⟶ N) (x y : D) :
    uncurryRight ((ForgetEnrichment.to (Complex A) M).map x y) ≫
      (leftModuleEvaluation A D y).map f =
    (𝟙 (x ⟶[Complex A] y) ⊗ₘ (leftModuleEvaluation A D x).map f) ≫
      uncurryRight ((ForgetEnrichment.to (Complex A) N).map x y) := by
  let τ := leftModuleClosedHomEquiv A D M N f
  have h := closedFamily_action_chain A
    (M := (ForgetEnrichment.to (Complex A) M).toRightOpposite)
    (N := (ForgetEnrichment.to (Complex A) N).toRightOpposite)
    (closedTransApp A τ) (closedTransApp_naturality A τ) (op (op x)) (op (op y))
  change uncurryRight (𝟙 _ ≫ (ForgetEnrichment.to (Complex A) M).map x y) ≫
      closedTransApp A τ (op (op y)) =
    (𝟙 (x ⟶[Complex A] y) ⊗ₘ closedTransApp A τ (op (op x))) ≫
      uncurryRight (𝟙 _ ≫ (ForgetEnrichment.to (Complex A) N).map x y) at h
  simpa only [Category.id_comp, leftModuleEvaluation_map] using h

end SerrePositivity.DifferentialGraded
end

end LeftMorphisms

/-! ## LeftClosedMaps（旧 SerrePositivity/DifferentialGraded/Module/LeftClosedMaps.lean） -/

/-! # 全Hom自然な成分族から左dg加群の閉零射を構成する -/

@[expose] public section LeftClosedMaps
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma leftFamily_rightOpposite_naturality {M N : LeftModule A D}
    (a : ∀ x, M.obj x ⟶ N.obj x)
    (h : ∀ x y, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) (x y : Dᵒᵖᵒᵖ) :
    M.toRightOpposite.map x y ≫ homPostcompose (M.toRightOpposite.obj x) (a y.unop.unop) =
      N.toRightOpposite.map x y ≫ homPrecompose (a x.unop.unop) (N.toRightOpposite.obj y) := by
  change (𝟙 _ ≫ M.map x.unop.unop y.unop.unop) ≫
    homPostcompose (M.obj x.unop.unop) (a y.unop.unop) =
    (𝟙 _ ≫ N.map x.unop.unop y.unop.unop) ≫
      homPrecompose (a x.unop.unop) (N.obj y.unop.unop)
  simpa only [Category.id_comp] using h x.unop.unop y.unop.unop

variable [Small.{u} D]

/-- 全次数自然な成分族から、既存の左加群Hom endの閉零射を作る。 -/
def leftModuleMorphismMk {M N : LeftModule A D}
    (a : ∀ x, M.obj x ⟶ N.obj x)
    (h : ∀ x y, M.map x y ≫ homPostcompose (M.obj x) (a y) =
      N.map x y ≫ homPrecompose (a x) (N.obj y)) :
    ForgetEnrichment.of (Complex A) M ⟶ ForgetEnrichment.of (Complex A) N :=
  ForgetEnrichment.homOf (Complex A)
    (ForgetEnrichment.homTo (Complex A)
      (moduleMorphismMk A Dᵒᵖ (M := M.toRightOpposite) (N := N.toRightOpposite)
        (fun x => a x.unop.unop) (leftFamily_rightOpposite_naturality A D a h)))

@[simp]
lemma leftModuleMorphismMk_eval {M N : LeftModule A D} (a) (h) (x : D) :
    (leftModuleEvaluation A D x).map (leftModuleMorphismMk A D (M := M) (N := N) a h) =
      a x := by
  change (moduleEvaluation A Dᵒᵖ (op x)).map
    (moduleMorphismMk A Dᵒᵖ (M := M.toRightOpposite) (N := N.toRightOpposite)
      (fun z => a z.unop.unop) (leftFamily_rightOpposite_naturality A D a h)) = a x
  exact moduleMorphismMk_eval A Dᵒᵖ _ _ (op x)

lemma leftModuleMorphism_ext {M N : LeftModuleCategory A D} {f g : M ⟶ N}
    (h : ∀ x, (leftModuleEvaluation A D x).map f = (leftModuleEvaluation A D x).map g) :
    f = g := by
  change ForgetEnrichment.homTo (Complex A) f = ForgetEnrichment.homTo (Complex A) g
  apply moduleHom_ext
  intro x
  exact (complexClosedHomEquiv A _ _).injective (h x.unop)

end SerrePositivity.DifferentialGraded
end

end LeftClosedMaps

/-! ## LeftYonedaFunctor（旧 SerrePositivity/DifferentialGraded/Module/LeftYonedaFunctor.lean） -/

/-! # 左representableの代表対象に関する全Hom写像 -/

@[expose] public section LeftYonedaFunctor
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]


/-- opposite上のYoneda拡張を二重opposite表示の全自然族へ移す。 -/
def leftYonedaParam (z z' : D) :
    ModuleParamTrans A Dᵒᵖ (op z ⟶[Complex A] op z')
      (leftRepresentable A z).toRightOpposite (leftRepresentable A z').toRightOpposite where
  app x := yonedaExtensionApp A (op z) (representable A (op z')) (𝟙 _) x
  naturality x y := by
    have h := yonedaExtensionApp_naturality A (op z) (representable A (op z')) (𝟙 _) x y
    change (β_ (op z ⟶[Complex A] op z') (x ⟶[Complex A] y)).hom ≫
        ((𝟙 _ ≫ 𝟙 _ ≫ representableMap A (op z) x y) ⊗ₘ
          yonedaExtensionApp A (op z) (representable A (op z')) (𝟙 _) y) ≫
            enrichedComposition _ _ _ =
      (yonedaExtensionApp A (op z) (representable A (op z')) (𝟙 _) x ⊗ₘ
        (𝟙 _ ≫ 𝟙 _ ≫ representableMap A (op z') x y)) ≫ enrichedComposition _ _ _
    simpa only [Category.id_comp] using h

/-- 反変に動く代表対象のHomを左加群の全Homへ送る。 -/
def leftYonedaHom (z z' : D) :
    (op z ⟶[Complex A] op z') ⟶ leftModuleHom A D (leftRepresentable A z)
      (leftRepresentable A z') :=
  (moduleHomEquiv A Dᵒᵖ _ _ _).symm (leftYonedaParam A D z z')

@[reassoc]
lemma leftYonedaHom_π (z z' x : D) :
    leftYonedaHom A D z z' ≫
      leftModuleHomπ A D (leftRepresentable A z) (leftRepresentable A z') x =
    yonedaExtensionApp A (op z) (representable A (op z')) (𝟙 _) (op (op x)) :=
  moduleHomEquiv_symm_π A Dᵒᵖ _ _ _ (leftYonedaParam A D z z') (op x)

lemma leftYonedaHom_element (z z' x : D) {p r n : ℤ}
    (f : GradedHom A (op z) (op z') p) (h : GradedHom A z x r) (hn : r + p = n) :
    (((leftModuleHomπ A D (leftRepresentable A z) (leftRepresentable A z') x).f p
      ((leftYonedaHom A D z z').f p f)).v r n hn) h =
    forward A (D := D) (x := z') (y := z) (z := x) f h (by omega) := by
  have hp := congrArg (fun t => t.f p f) (leftYonedaHom_π A D z z' x)
  change (leftModuleHomπ A D (leftRepresentable A z) (leftRepresentable A z') x).f p
    ((leftYonedaHom A D z z').f p f) = _ at hp
  rw [hp]
  have he := yonedaExtensionApp_apply A (op z) (representable A (op z')) (𝟙 _)
    (op (op x)) p r n hn f h
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply] at he
  change (((yonedaExtensionApp A (op z) (representable A (op z')) (𝟙 _) (op (op x))).f p f).v
      r n hn) h =
    (p * r).negOnePow • forward A (D := Dᵒᵖ) (x := op x) (y := op z) (z := op z') h f hn at he
  rw [opposite_forward, mul_comm r p, smul_smul, Int.units_mul_self, one_smul] at he
  exact he

end SerrePositivity.DifferentialGraded
end

end LeftYonedaFunctor

/-! ## LeftMapNaturality（旧 SerrePositivity/DifferentialGraded/Module/LeftMapNaturality.lean） -/

/-! # 左dg加群の閉零射の全Hom自然性をchain mapの式で読む

## 概要
左dg加群の閉零射の全Hom自然性をchain mapの式で読む。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/TensorModuleMaps.lean。dg加群の導来作用・準同値比較の基盤。
任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section LeftMapNaturality
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma leftModuleMorphism_naturality {M N : LeftModuleCategory A D} (f : M ⟶ N) (x y : D) :
    (ForgetEnrichment.to (Complex A) M).map x y ≫
      homPostcompose ((ForgetEnrichment.to (Complex A) M).obj x)
        ((leftModuleEvaluation A D y).map f) =
    (ForgetEnrichment.to (Complex A) N).map x y ≫
      homPrecompose ((leftModuleEvaluation A D x).map f)
        ((ForgetEnrichment.to (Complex A) N).obj y) := by
  have h := closedTransApp_naturality A (leftModuleClosedHomEquiv A D M N f)
    (op (op x)) (op (op y))
  change (𝟙 _ ≫ (ForgetEnrichment.to (Complex A) M).map x y) ≫
      homPostcompose ((ForgetEnrichment.to (Complex A) M).obj x)
        ((leftModuleEvaluation A D y).map f) =
    (𝟙 _ ≫ (ForgetEnrichment.to (Complex A) N).map x y) ≫
      homPrecompose ((leftModuleEvaluation A D x).map f)
        ((ForgetEnrichment.to (Complex A) N).obj y) at h
  simpa only [Category.id_comp] using h

end SerrePositivity.DifferentialGraded
end

end LeftMapNaturality

/-! ## ShiftCoherence（旧 SerrePositivity/DifferentialGraded/Module/ShiftCoherence.lean） -/

/-! # 加群の零・加法 shift 比較と整合性 -/

@[expose] public section ShiftCoherence
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- Mathlib の零 shift 比較の全次数自然な加群同型への持ち上げ。 -/
def moduleShiftZeroIsoObj (M : RightModule A D) :
    ForgetEnrichment.of (Complex A) (shiftModule 0 M) ≅ ForgetEnrichment.of (Complex A) M :=
  moduleIsoMk A D (M := shiftModule 0 M) (N := M)
    (fun x => (shiftFunctorZero (Complex A) ℤ).app (M.obj x)) (by
      intro x y
      change (M.map x y ≫ shiftHom 0 (M.obj x) (M.obj y)) ≫
        homPostcompose ((M.obj x)⟦(0 : ℤ)⟧)
          ((shiftFunctorZero (Complex A) ℤ).hom.app (M.obj y)) = _
      rw [Category.assoc, shiftHom_zero_naturality]
      rfl)

/-- Mathlib の加法 shift 比較の全次数自然な加群同型への持ち上げ。 -/
def moduleShiftAddIsoObj (s t : ℤ) (M : RightModule A D) :
    ForgetEnrichment.of (Complex A) (shiftModule (s + t) M) ≅
      ForgetEnrichment.of (Complex A) (shiftModule t (shiftModule s M)) :=
  moduleIsoMk A D (M := shiftModule (s + t) M) (N := shiftModule t (shiftModule s M))
    (fun x => (shiftFunctorAdd (Complex A) s t).app (M.obj x)) (by
      intro x y
      change (M.map x y ≫ shiftHom (s + t) (M.obj x) (M.obj y)) ≫
        homPostcompose ((M.obj x)⟦s + t⟧)
          ((shiftFunctorAdd (Complex A) s t).hom.app (M.obj y)) =
        ((M.map x y ≫ shiftHom s (M.obj x) (M.obj y)) ≫
          shiftHom t ((M.obj x)⟦s⟧) ((M.obj y)⟦s⟧)) ≫
            homPrecompose ((shiftFunctorAdd (Complex A) s t).hom.app (M.obj x))
              (((M.obj y)⟦s⟧)⟦t⟧)
      simp only [Category.assoc]
      rw [shiftHom_add_naturality])

@[simp] lemma moduleShiftZeroIsoObj_hom_eval (M : RightModule A D) (x : D) :
    (moduleEvaluation A D x).map (moduleShiftZeroIsoObj A D M).hom =
      (shiftFunctorZero (Complex A) ℤ).hom.app (M.obj (op x)) :=
  moduleIsoMk_hom_eval A D _ _ x
@[simp] lemma moduleShiftZeroIsoObj_inv_eval (M : RightModule A D) (x : D) :
    (moduleEvaluation A D x).map (moduleShiftZeroIsoObj A D M).inv =
      (shiftFunctorZero (Complex A) ℤ).inv.app (M.obj (op x)) :=
  moduleIsoMk_inv_eval A D _ _ x
@[simp] lemma moduleShiftAddIsoObj_hom_eval (s t : ℤ) (M : RightModule A D) (x : D) :
    (moduleEvaluation A D x).map (moduleShiftAddIsoObj A D s t M).hom =
      (shiftFunctorAdd (Complex A) s t).hom.app (M.obj (op x)) :=
  moduleIsoMk_hom_eval A D _ _ x
@[simp] lemma moduleShiftAddIsoObj_inv_eval (s t : ℤ) (M : RightModule A D) (x : D) :
    (moduleEvaluation A D x).map (moduleShiftAddIsoObj A D s t M).inv =
      (shiftFunctorAdd (Complex A) s t).inv.app (M.obj (op x)) :=
  moduleIsoMk_inv_eval A D _ _ x

/-- 加群の零 shift 比較自然同型。 -/
def moduleShiftZeroIso : moduleShiftFunctor A D 0 ≅ 𝟭 (ModuleCategory A D) :=
  NatIso.ofComponents (fun M => moduleShiftZeroIsoObj A D (ForgetEnrichment.to (Complex A) M))
    (by
      intro M N f
      apply moduleMorphism_ext
      intro x
      simp only [moduleShiftFunctor, Functor.id_map,
        CategoryTheory.Functor.map_comp, moduleShiftMap_eval,
        moduleShiftZeroIsoObj_hom_eval]
      exact (shiftFunctorZero (Complex A) ℤ).hom.naturality ((moduleEvaluation A D x).map f))

/-- 加群の加法 shift 比較自然同型。 -/
def moduleShiftAddIso (s t : ℤ) :
    moduleShiftFunctor A D (s + t) ≅ moduleShiftFunctor A D s ⋙ moduleShiftFunctor A D t :=
  NatIso.ofComponents (fun M => moduleShiftAddIsoObj A D s t
    (ForgetEnrichment.to (Complex A) M)) (by
      intro M N f
      apply moduleMorphism_ext
      intro x
      simp only [moduleShiftFunctor, Functor.comp_map,
        CategoryTheory.Functor.map_comp, moduleShiftMap_eval,
        moduleShiftAddIsoObj_hom_eval]
      exact (shiftFunctorAdd (Complex A) s t).hom.naturality ((moduleEvaluation A D x).map f))

@[simp] lemma moduleShiftFunctor_map_eval (s : ℤ) {M N : ModuleCategory A D}
    (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map ((moduleShiftFunctor A D s).map f) =
      ((moduleEvaluation A D x).map f)⟦s⟧' := moduleShiftMap_eval A D s f x

@[simp] lemma moduleShiftZeroIso_hom_eval (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map ((moduleShiftZeroIso A D).hom.app M) =
      (shiftFunctorZero (Complex A) ℤ).hom.app ((moduleEvaluation A D x).obj M) :=
  moduleShiftZeroIsoObj_hom_eval A D _ x
@[simp] lemma moduleShiftZeroIso_inv_eval (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map ((moduleShiftZeroIso A D).inv.app M) =
      (shiftFunctorZero (Complex A) ℤ).inv.app ((moduleEvaluation A D x).obj M) :=
  moduleShiftZeroIsoObj_inv_eval A D _ x
@[simp] lemma moduleShiftAddIso_hom_eval (s t : ℤ) (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map ((moduleShiftAddIso A D s t).hom.app M) =
      (shiftFunctorAdd (Complex A) s t).hom.app ((moduleEvaluation A D x).obj M) :=
  moduleShiftAddIsoObj_hom_eval A D s t _ x
@[simp] lemma moduleShiftAddIso_inv_eval (s t : ℤ) (M : ModuleCategory A D) (x : D) :
    (moduleEvaluation A D x).map ((moduleShiftAddIso A D s t).inv.app M) =
      (shiftFunctorAdd (Complex A) s t).inv.app ((moduleEvaluation A D x).obj M) :=
  moduleShiftAddIsoObj_inv_eval A D s t _ x

/-- 加群 shift の零・加法比較は複体 shift の整合性を満たす。 -/
def moduleShiftMkCore : ShiftMkCore (ModuleCategory A D) ℤ where
  F := moduleShiftFunctor A D
  zero := moduleShiftZeroIso A D
  add := moduleShiftAddIso A D
  assoc_hom_app s t r M := by
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, moduleShiftFunctor_map_eval,
      moduleShiftAddIso_hom_eval, eqToHom_map]
    change (shiftFunctorAdd (Complex A) (s + t) r).hom.app
        ((moduleEvaluation A D x).obj M) ≫
      ((shiftFunctorAdd (Complex A) s t).hom.app ((moduleEvaluation A D x).obj M))⟦r⟧' =
      eqToHom (congrArg (fun n : ℤ => ((moduleEvaluation A D x).obj M)⟦n⟧)
        (add_assoc s t r)) ≫
      (shiftFunctorAdd (Complex A) s (t + r)).hom.app ((moduleEvaluation A D x).obj M) ≫
      (shiftFunctorAdd (Complex A) t r).hom.app (((moduleEvaluation A D x).obj M)⟦s⟧)
    have h := shiftFunctorAdd_assoc_hom_app s t r ((moduleEvaluation A D x).obj M)
    simpa only [shiftFunctorAdd', Iso.trans_hom, NatTrans.comp_app,
      eqToIso.hom, eqToHom_app, Category.assoc] using h
  zero_add_hom_app s M := by
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, moduleShiftFunctor_map_eval,
      moduleShiftAddIso_hom_eval, moduleShiftZeroIso_inv_eval, eqToHom_map]
    exact shiftFunctorAdd_zero_add_hom_app s ((moduleEvaluation A D x).obj M)
  add_zero_hom_app s M := by
    apply moduleMorphism_ext
    intro x
    simp only [CategoryTheory.Functor.map_comp, moduleShiftAddIso_hom_eval,
      moduleShiftZeroIso_inv_eval, eqToHom_map]
    exact shiftFunctorAdd_add_zero_hom_app s ((moduleEvaluation A D x).obj M)

/-- 閉零 dg 加群圏の整数 shift。整合性は Mathlib の比較から証明した。 -/
instance moduleHasShift : HasShift (ModuleCategory A D) ℤ :=
  hasShiftMk _ _ (moduleShiftMkCore A D)

/-- 登録された shift は明示構成した関手と同じ。 -/
lemma moduleShiftFunctor_eq (s : ℤ) :
    CategoryTheory.shiftFunctor (ModuleCategory A D) s = moduleShiftFunctor A D s := rfl

lemma moduleShiftZero_eq :
    shiftFunctorZero (ModuleCategory A D) ℤ = moduleShiftZeroIso A D := rfl
lemma moduleShiftAdd_eq (s t : ℤ) :
    shiftFunctorAdd (ModuleCategory A D) s t = moduleShiftAddIso A D s t := rfl

/-- 加群の各整数 shift は加法的。 -/
instance moduleShiftFunctorAdditive (s : ℤ) : (moduleShiftFunctor A D s).Additive where
  map_add := by
    intro M N f g
    apply moduleMorphism_ext
    intro x
    simp only [moduleShiftFunctor_map_eval, Functor.map_add]

/-- 登録された整数 shift も加法的。 -/
instance moduleShiftAdditive (s : ℤ) :
    (CategoryTheory.shiftFunctor (ModuleCategory A D) s).Additive :=
  moduleShiftFunctorAdditive A D s

/-- 評価比較は零・加法 shift と整合する。 -/
instance moduleEvaluationCommShift (x : D) : (moduleEvaluation A D x).CommShift ℤ where
  commShiftIso := fun s => moduleShiftEvaluationIso A D s x
  commShiftIso_zero := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simp only [moduleShiftEvaluationIso, NatIso.ofComponents_hom_app,
      Functor.CommShift.isoZero_hom_app, moduleShiftZero_eq,
      moduleShiftZeroIso_hom_eval, Iso.hom_inv_id_app, Iso.refl_hom]
    rfl
  commShiftIso_add s t := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simp only [Functor.CommShift.isoAdd_hom_app, moduleShiftAdd_eq,
      moduleShiftAddIso_hom_eval, moduleShiftEvaluationIso, NatIso.ofComponents_hom_app,
      Iso.refl_hom]
    change 𝟙 (((moduleEvaluation A D x).obj M)⟦s + t⟧) =
      (shiftFunctorAdd (Complex A) s t).hom.app ((moduleEvaluation A D x).obj M) ≫
      𝟙 ((((moduleEvaluation A D x).obj M)⟦s⟧)⟦t⟧) ≫
      (𝟙 (((moduleEvaluation A D x).obj M)⟦s⟧))⟦t⟧' ≫
      (shiftFunctorAdd (Complex A) s t).inv.app ((moduleEvaluation A D x).obj M)
    simp only [CategoryTheory.Functor.map_id]
    change 𝟙 _ = (shiftFunctorAdd (Complex A) s t).hom.app
        ((moduleEvaluation A D x).obj M) ≫
      𝟙 ((CategoryTheory.shiftFunctor (Complex A) s ⋙
        CategoryTheory.shiftFunctor (Complex A) t).obj ((moduleEvaluation A D x).obj M)) ≫
      (shiftFunctorAdd (Complex A) s t).inv.app ((moduleEvaluation A D x).obj M)
    rw [Category.id_comp]
    exact (Iso.hom_inv_id_app (shiftFunctorAdd (Complex A) s t) _).symm
end SerrePositivity.DifferentialGraded
end

end ShiftCoherence
