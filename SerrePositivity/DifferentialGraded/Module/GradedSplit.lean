module
public import SerrePositivity.DifferentialGraded.Module.Action
public import SerrePositivity.DifferentialGraded.Module.Category
public import SerrePositivity.DifferentialGraded.Module.Zero
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # 全次数作用に関して分裂するdg加群の拡大

section/retractionにchain map条件は課さない。微分を忘れた次数付き加群での分裂を記録する。
主dg加群モデルは変更しない。
-/
@[expose] public section
noncomputable section
universe u v
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
