module
public import SerrePositivity.DifferentialGraded.Tensor.Semifree

/-! # local A-K-flat Homの下でのobjectwise K-flat性

相対K-flat性とは別の条件を使い、Hom複体のK-flat仮定をこの結果にだけ置く。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

/-- A上K-flat性は次数ごと分裂する複体拡張で閉じる。 -/
lemma complexKFlat_of_degreewiseSplit (S : ShortComplex (Complex A))
    (σ : ∀ n, (S.map (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n)).Splitting)
    (h₁ : complexKFlat A S.X₁) (h₃ : complexKFlat A S.X₃) : complexKFlat A S.X₂ := by
  intro L hL
  exact cochainTensor_acyclic_of_degreewiseSplit S σ L (h₁ L hL) (h₃ L hL)

variable (D : Type v) [DGCategory A D]

/-- 各Hom複体のA上K-flat性。対象集合のsmallnessとは独立。 -/
def localHomKFlat : Prop := ∀ x y : D, complexKFlat A (x ⟶[Complex A] y)

/-- 右dg加群の各評価複体のA上K-flat性。相対条件とは区別する。 -/
def moduleObjectwiseKFlat (M : RightModule A D) : Prop :=
  ∀ x : D, complexKFlat A (M.obj (Opposite.op x))

variable [Small.{u} D]

/-- local HomがA上K-flatなら、K-flat生成複体による自由加群はobjectwise K-flat。 -/
lemma freeAt_objectwiseKFlat (hD : localHomKFlat A D) (x : D) (K : Complex A)
    (hK : complexKFlat A K) :
    moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) ((freeAt x).obj K)) := by
  intro y
  exact complexKFlat_tensor A hK (hD y x)

/-- 評価が余極限を保つことを使うobjectwise K-flat性のexact余極限閉性。 -/
lemma moduleObjectwiseKFlat_colimit {J : Type w} [Category.{w'} J] [Small.{u} J]
    [HasExactColimitsOfShape J (ModuleCat.{u} A)] (F : J ⥤ ModuleCategory A D)
    (h : ∀ j, moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) (F.obj j))) :
    moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) (colimit F)) := by
  intro x
  have hc := complexKFlat_colimit A (F ⋙ moduleEvaluation A D x) (fun j => h j x)
  exact complexKFlat_of_iso A (moduleEvaluationColimitIso A D F x) hc

/-- 全作用に関するgraded-split拡張はobjectwise K-flat性を保つ。 -/
lemma moduleObjectwiseKFlat_of_gradedSplit {M N P : ModuleCategory A D}
    {f : M ⟶ N} {g : N ⟶ P} (s : ModuleGradedSplit A D f g)
    (hM : moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) M))
    (hP : moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) P)) :
    moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) N) := by
  intro x
  let S : ShortComplex (Complex A) := ShortComplex.mk
    ((moduleEvaluation A D x).map f) ((moduleEvaluation A D x).map g) (by
      rw [← CategoryTheory.Functor.map_comp, s.inclusion_projection,
        CategoryTheory.Functor.map_zero])
  have σ : ∀ n, (S.map (HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) n)).Splitting :=
    fun n =>
      { r := s.retraction x n
        s := s.section_ x n
        f_r := s.inclusion_retraction x n
        s_g := s.section_projection x n
        id := s.decomposition x n }
  exact complexKFlat_of_degreewiseSplit A S σ (hM x) (hP x)

/-- sphere-free表示のobjectwise結果にだけlocal HomのA上K-flat性を要求する。 -/
lemma sphereFreePresentation_objectwiseKFlat (hD : localHomKFlat A D)
    {M : ModuleCategory A D} (S : ModuleSphereFreePresentation A D M) :
    moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) M) := by
  have := S.smallIndex
  have : HasExactColimitsOfShape (Discrete S.Index) (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (Discrete.equivalence (equivShrink.{u} S.Index).symm)
  have hc := moduleObjectwiseKFlat_colimit A D
    (Discrete.functor fun i => freeSphere A D (S.object i) (S.degree i))
    (fun i => freeAt_objectwiseKFlat A D hD (S.object i.as) _ (complexSphere_kFlat A _))
  intro x
  exact complexKFlat_of_iso A ((moduleEvaluation A D x).mapIso S.iso) (hc x)

/-- local K-flat Homの下でsemifree filtrationの各段階はobjectwise K-flat。 -/
lemma ModuleSemifreeFiltration.objectwiseKFlat_stage (hD : localHomKFlat A D)
    {M : ModuleCategory A D} (F : ModuleSemifreeFiltration A D M) (n : ℕ) :
    moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) (F.stage n)) := by
  induction n with
  | zero => exact sphereFreePresentation_objectwiseKFlat A D hD F.initial
  | succ n ih =>
    exact moduleObjectwiseKFlat_of_gradedSplit A D (F.split n) ih
      (sphereFreePresentation_objectwiseKFlat A D hD (F.quotientPresentation n))

/-- local K-flat Homの下でsemifree加群はobjectwise K-flat。 -/
lemma moduleSemifree_objectwiseKFlat (hD : localHomKFlat A D)
    {M : ModuleCategory A D} (hM : moduleSemifree A D M) :
    moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) M) := by
  obtain ⟨F⟩ := hM
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_of_univLE (ModuleCat.{u} A)
  have hc := moduleObjectwiseKFlat_colimit A D (Functor.ofSequence F.transition)
    (fun n => F.objectwiseKFlat_stage A D hD n)
  let e : colimit (Functor.ofSequence F.transition) ≅ M :=
    (colimit.isColimit _).coconePointUniqueUpToIso F.isColimit ≪≫ F.iso
  intro x
  exact complexKFlat_of_iso A ((moduleEvaluation A D x).mapIso e).symm (hc x)

/-- local K-flat Homの下では相対/評価ごとの両条件を満たすsemifree解像度を取れる。 -/
theorem exists_objectwiseKFlat_resolution (hD : localHomKFlat A D) (M : ModuleCategory A D) :
    ∃ (P : ModuleCategory A D) (q : P ⟶ M),
      moduleSemifree A D P ∧ moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) P) ∧
        moduleObjectwiseKFlat A D (ForgetEnrichment.to (Complex A) P) ∧
        moduleDegreewiseSurjective A D q ∧ moduleQuasiIso A D q := by
  obtain ⟨P, q, hP, hk, hs, hq⟩ := exists_relativeKFlat_resolution A D M
  exact ⟨P, q, hP, hk, moduleSemifree_objectwiseKFlat A D hD hP, hs, hq⟩

end SerrePositivity.DifferentialGraded
