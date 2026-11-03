module

public import SerrePositivity.DifferentialGraded.Verdier.Scalar
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import SerrePositivity.DifferentialGraded.Derived.Projective
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology
public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.DifferentialGraded.Morita.Kernel
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import SerrePositivity.DifferentialGraded.Tensor.Triple
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKernel
public import SerrePositivity.DifferentialGraded.Endomorphism.Shift

/-!
# Morita.CriterionPerfTriangulated

## 概要
16 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## CriterionPerfTriangulated（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerfTriangulated.lean） -/

/-! # Perf 上の Morita 判定で使う一般 kernel 作用の三角性

実際の主導来作用を保持し、入力の射影的ホモトピー圏上の tensor 計算から得た
既存の shift・三角性を公開する。一般 kernel の右随伴は使わない。
-/

@[expose] public section CriterionPerfTriangulated
universe u v w

noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)

/-- 一般 kernel の実際の作用に対する、tensor 計算由来の整数 shift 構造。 -/
@[instance_reducible]
def criterionPerfKernelCommShift : (kernelDerivedTensor A D E K).CommShift ℤ :=
  mainKernelActionCommShift A D E K

/-- 一般 kernel の主導来作用は完全三角形を保存する。平坦性条件は不要。 -/
lemma criterionPerfKernelIsTriangulated :
    letI := criterionPerfKernelCommShift A D E K
    (kernelDerivedTensor A D E K).IsTriangulated :=
  mainKernelActionIsTriangulated A D E K

/-- 完全三角形の保存を、選択した shift と実際の作用関手について明記する。 -/
lemma criterionPerfKernel_map_distinguished
    (Δ : Triangle (DerivedModuleCategory A D))
    (hΔ : Δ ∈ distTriang (DerivedModuleCategory A D)) :
    letI := criterionPerfKernelCommShift A D E K
    (kernelDerivedTensor A D E K).mapTriangle.obj Δ ∈ distTriang (DerivedModuleCategory A E) := by
  let := criterionPerfKernelCommShift A D E K
  let := criterionPerfKernelIsTriangulated A D E K
  exact (kernelDerivedTensor A D E K).map_distinguished Δ hΔ

variable (hK : kernelColumnsPerfect A D E K)

/-- 列の perfect 性だけを使う、実際の Perf 制限の整数 shift。 -/
@[instance_reducible]
def criterionPerfActionCommShift : (perfectDerivedKernelAction A D E K hK).CommShift ℤ :=
  mainPerfectKernelActionCommShift A D E K hK

lemma criterionPerfActionIsTriangulated :
    letI := criterionPerfActionCommShift A D E K hK
    (perfectDerivedKernelAction A D E K hK).IsTriangulated :=
  mainPerfectKernelActionIsTriangulated A D E K hK

/-- 第一条件の列の perfect 性は、実際の主作用が Perf を保つことと同値。 -/
lemma criterionPerfColumns_iff_preservesPerfect :
    kernelColumnsPerfect A D E K ↔
      ∀ X, modulePerfect A D X → modulePerfect A E ((kernelDerivedTensor A D E K).obj X) :=
  kernelColumnsPerfect_iff_preservesPerfect A D E K
end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerfTriangulated

/-! ## CriterionPerfGeneration（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerfGeneration.lean） -/

/-! # Perf 判定の生成条件と本質像の厚さ

厚い生成性を他の二条件とは独立に定義する。生成対象の任意余積は要求しない。
-/

@[expose] public section CriterionPerfGeneration
universe u v w u₁ u₂ v₁ v₂

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Pretriangulated

/-- 冪等完備な圏からの充満忠実関手の本質像は retract に閉じる。 -/
lemma criterionPerfEssImage_retract_closed
    {C : Type u₁} [Category.{v₁} C] [IsIdempotentComplete C]
    {T : Type u₂} [Category.{v₂} T] (F : C ⥤ T) [F.Full] [F.Faithful] :
    F.essImage.IsStableUnderRetracts where
  of_retract {Z Y} t hY := by
    obtain ⟨X, ⟨e⟩⟩ := hY
    let a : Retract Z (F.obj X) := t.trans (Retract.ofIso e.symm)
    let p : X ⟶ X := F.preimage (a.r ≫ a.i)
    have hp : F.map p = a.r ≫ a.i := F.map_preimage _
    have hpp : p ≫ p = p := by
      apply F.map_injective
      rw [F.map_comp, hp]
      simp only [Category.assoc, a.retract_assoc]
    obtain ⟨X', i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split X p hpp
    have hi : i ≫ p = i := by rw [← hri, ← Category.assoc, hir, Category.id_comp]
    refine ⟨X', ⟨{
      hom := F.map i ≫ a.r
      inv := a.i ≫ F.map r
      hom_inv_id := ?_
      inv_hom_id := ?_ }⟩⟩
    · calc
        (F.map i ≫ a.r) ≫ (a.i ≫ F.map r) = F.map (i ≫ p ≫ r) := by
          simp only [F.map_comp, hp, Category.assoc]
        _ = 𝟙 _ := by rw [← Category.assoc, hi, hir, F.map_id]
    · calc
        (a.i ≫ F.map r) ≫ (F.map i ≫ a.r) = a.i ≫ F.map p ≫ a.r := by
          rw [← hri, F.map_comp]
          simp only [Category.assoc]
        _ = 𝟙 _ := by simp only [hp, Category.assoc, a.retract_assoc, a.retract]

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)

local instance : (perfectModuleInclusion A E Set.univ).Full :=
  inferInstanceAs ((modulePerfect A E).ι.Full)
local instance : (perfectModuleInclusion A E Set.univ).Faithful :=
  inferInstanceAs ((modulePerfect A E).ι.Faithful)

/-- 各列を含む厚い部分圏は Perf(E) を含む。列の perfect 性は別条件。 -/
def criterionPerfColumnsThickGenerate : Prop :=
  ∀ (P : ObjectProperty (DerivedModuleCategory A E)),
    P.IsTriangulated → P.IsClosedUnderIsomorphisms → P.IsStableUnderRetracts →
    (∀ d : D, P ((kernelDerivedColumn A D E d).obj K)) → modulePerfect A E ≤ P

/-- 作用の像を含む厚い性質は、列を含むかどうかだけで決まる。 -/
lemma criterionPerf_image_le_iff_columns
    (P : ObjectProperty (DerivedModuleCategory A E)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] [P.IsStableUnderRetracts] :
    (∀ X, modulePerfect A D X → P ((kernelDerivedTensor A D E K).obj X)) ↔
      ∀ d : D, P ((kernelDerivedColumn A D E d).obj K) := by
  let := criterionPerfKernelCommShift A D E K
  let := criterionPerfKernelIsTriangulated A D E K
  let : (P.inverseImage (kernelDerivedTensor A D E K)).IsStableUnderRetracts :=
    ⟨fun t ht => P.prop_of_retract (t.map (kernelDerivedTensor A D E K)) ht⟩
  constructor
  · intro h d
    exact P.prop_of_iso (kernelDerivedColumnActionIso A D E K d)
      (h _ (modulePerfectOver_representable A D d (Set.mem_univ d)))
  · intro h
    exact (modulePerfect_le_iff_generators A D (P.inverseImage
      (kernelDerivedTensor A D E K))).2 (fun d =>
        P.prop_of_iso (kernelDerivedColumnActionIso A D E K d).symm (h d))

/-- 充満忠実性を確保した後は、厚い生成性だけで Perf 上の本質的全射が従う。 -/
lemma criterionPerf_essSurj_of_columnsThickGenerate
    (hK : kernelColumnsPerfect A D E K)
    [(perfectDerivedKernelAction A D E K hK).Full]
    [(perfectDerivedKernelAction A D E K hK).Faithful]
    (hgen : criterionPerfColumnsThickGenerate A D E K) :
    (perfectDerivedKernelAction A D E K hK).EssSurj := by
  let F := perfectDerivedKernelAction A D E K hK
  let := criterionPerfActionCommShift A D E K hK
  let := criterionPerfActionIsTriangulated A D E K hK
  let G := F ⋙ perfectModuleInclusion A E Set.univ
  let : G.essImage.IsStableUnderRetracts := criterionPerfEssImage_retract_closed G
  have hcols : ∀ d : D, G.essImage ((kernelDerivedColumn A D E d).obj K) := by
    intro d
    exact ⟨⟨_, modulePerfectOver_representable A D d (Set.mem_univ d)⟩,
      ⟨kernelDerivedColumnActionIso A D E K d⟩⟩
  have hle := hgen G.essImage inferInstance inferInstance inferInstance hcols
  refine ⟨fun Y => ?_⟩
  obtain ⟨X, ⟨e⟩⟩ := hle Y.obj Y.property
  exact ⟨X, ⟨(perfectModuleInclusion A E Set.univ).preimageIso e⟩⟩

/-- 本質的全射な実際の Perf 作用の列は Perf(E) を厚く生成する。 -/
lemma criterionPerf_columnsThickGenerate_of_essSurj
    (hK : kernelColumnsPerfect A D E K)
    [(perfectDerivedKernelAction A D E K hK).EssSurj] :
    criterionPerfColumnsThickGenerate A D E K := by
  intro P htri hiso hret hcols Y hY
  let F := perfectDerivedKernelAction A D E K hK
  have himage := (criterionPerf_image_le_iff_columns A D E K P).2 hcols
  let Y' : PerfectModuleCategory A E := ⟨Y, hY⟩
  let X := F.objPreimage Y'
  exact P.prop_of_iso
    ((perfectModuleInclusion A E Set.univ).mapIso (F.objObjPreimageIso Y'))
    (himage X.obj X.property)

/-- Perf 上では任意余積による生成性は不要で、厚い生成性で足りる。 -/
lemma criterionPerf_essSurj_iff_columnsThickGenerate
    (hK : kernelColumnsPerfect A D E K)
    [(perfectDerivedKernelAction A D E K hK).Full]
    [(perfectDerivedKernelAction A D E K hK).Faithful] :
    (perfectDerivedKernelAction A D E K hK).EssSurj ↔
      criterionPerfColumnsThickGenerate A D E K := by
  constructor
  · intro h
    exact criterionPerf_columnsThickGenerate_of_essSurj A D E K hK
  · exact criterionPerf_essSurj_of_columnsThickGenerate A D E K hK

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerfGeneration

/-! ## CriterionPerfEquivalence（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerfEquivalence.lean） -/

/-! # 実際の kernel 作用が Perf 上の同値であることの証拠

同値（逆関手と二つの自然同型を含む）と、主導来作用との比較を保持する。
一般 kernel の右随伴は構成しない。
-/

@[expose] public section CriterionPerfEquivalence
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)

/-- 任意の圏同値ではなく、実際の主作用に一致する Perf 同値の証拠。 -/
structure CriterionPerfEquivalenceWitness where
  equivalence : PerfectModuleCategory A D ≌ PerfectModuleCategory A E
  comparison : perfectModuleInclusion A D Set.univ ⋙ kernelDerivedTensor A D E K ≅
    equivalence.functor ⋙ perfectModuleInclusion A E Set.univ

variable (W : CriterionPerfEquivalenceWitness A D E K)
include W

/-- 同値との比較だけで、列の perfect 性が必要になる。 -/
lemma CriterionPerfEquivalenceWitness.columnsPerfect : kernelColumnsPerfect A D E K := by
  apply (kernelColumnsPerfect_iff_preservesPerfect A D E K).2
  intro X hX
  exact (modulePerfect A E).prop_of_iso (W.comparison.app ⟨X, hX⟩).symm
    (W.equivalence.functor.obj ⟨X, hX⟩).property

local instance : (perfectModuleInclusion A E Set.univ).Full :=
  inferInstanceAs ((modulePerfect A E).ι.Full)
local instance : (perfectModuleInclusion A E Set.univ).Faithful :=
  inferInstanceAs ((modulePerfect A E).ι.Faithful)

/-- 列の perfect 性から得た実際の制限と、証拠に含まれる同値との自然同型。 -/
def CriterionPerfEquivalenceWitness.actionIso :
    perfectDerivedKernelAction A D E K (W.columnsPerfect A D E K) ≅ W.equivalence.functor :=
  Functor.fullyFaithfulCancelRight (perfectModuleInclusion A E Set.univ)
    (perfectDerivedKernelActionInclusionIso A D E K _ ≪≫ W.comparison)

/-- 実際の制限も圏同値である。 -/
lemma CriterionPerfEquivalenceWitness.actionIsEquivalence :
    (perfectDerivedKernelAction A D E K (W.columnsPerfect A D E K)).IsEquivalence :=
  Functor.isEquivalence_of_iso (W.actionIso A D E K).symm

/-- 同値の必要条件としての厚い生成性。 -/
lemma CriterionPerfEquivalenceWitness.columnsThickGenerate :
    criterionPerfColumnsThickGenerate A D E K := by
  let := W.actionIsEquivalence A D E K
  exact criterionPerf_columnsThickGenerate_of_essSurj A D E K (W.columnsPerfect A D E K)

omit W in
/-- 充満忠実性と厚い生成性が揃った実際の制限から、同値の証拠を取り出す。 -/
def criterionPerfEquivalenceWitnessOfFullyFaithful
    (hK : kernelColumnsPerfect A D E K)
    [(perfectDerivedKernelAction A D E K hK).Full]
    [(perfectDerivedKernelAction A D E K hK).Faithful]
    (hgen : criterionPerfColumnsThickGenerate A D E K) :
    CriterionPerfEquivalenceWitness A D E K := by
  let := criterionPerf_essSurj_of_columnsThickGenerate A D E K hK hgen
  let : (perfectDerivedKernelAction A D E K hK).IsEquivalence := {}
  exact ⟨(perfectDerivedKernelAction A D E K hK).asEquivalence,
    (perfectDerivedKernelActionInclusionIso A D E K hK).symm⟩

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerfEquivalence

/-! ## CriterionPerfHomComparison（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerfHomComparison.lean） -/

/-! # Kernel の左作用から導来全 Hom への比較

源の列だけを射影置換する。標的の列は置換する必要がなく、列自体の射影性も
仮定しない。比較は全次数の複体射であり、次数零の Hom 集合ではない。
-/

@[expose] public section CriterionPerfHomComparison
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- 列を通常の dg 加群の圏の対象として読む。 -/
abbrev criterionPerfColumn (d : D) : ModuleCategory A E :=
  ForgetEnrichment.of (Complex A) (P.rightAt d)

/-- 左作用の後で、源の列の増強により前合成した実際の複体射。 -/
def criterionPerfHomComparison (d d' : D)
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    homObject A D d d' ⟶
      homObject A (RightModule A E) R.obj (criterionPerfColumn A D E P d') :=
  P.toFunctor.map d d' ≫ eHomWhiskerRight (Complex A) R.π
    (criterionPerfColumn A D E P d')

/-- 標準解像度を使った、全 Hom 複体の擬同型条件。 -/
def criterionPerfFullHomQuasiIso : Prop :=
  ∀ d d' : D, QuasiIso (criterionPerfHomComparison A D E P d d'
    (moduleCanonicalProjectiveResolution A E (criterionPerfColumn A D E P d)))

/-- 比較の終域の次数零ホモロジーは、実際の導来圏の列間の射を計算する。 -/
def criterionPerfColumnDerivedHomEquiv (d d' : D)
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    ((moduleToDerived A E).obj (criterionPerfColumn A D E P d) ⟶
        (moduleToDerived A E).obj (criterionPerfColumn A D E P d')) ≃
      (homObject A (RightModule A E) R.obj (criterionPerfColumn A D E P d')).homology 0 := by
  letI := moduleToDerived_inverts A E R.π R.quasiIso
  exact (Iso.homCongr (asIso ((moduleToDerived A E).map R.π)).symm (Iso.refl _)).trans
    (moduleProjectiveDerivedHomologyEquiv A E R.projective _)

/-- 異なる解像度の比較は全 Hom 複体上でホモトピー可換。 -/
def criterionPerfHomComparison_resolution_homotopy (d d' : D)
    (R S : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    Homotopy
      (criterionPerfHomComparison A D E P d d' S ≫
        eHomWhiskerRight (Complex A) (R.comparison S) (criterionPerfColumn A D E P d'))
      (criterionPerfHomComparison A D E P d d' R) := by
  have h : Nonempty (ModuleHomotopy A E (R.comparison S ≫ S.π) R.π) := by
    apply (moduleToHomotopy_map_eq_iff A E _ _).1
    rw [CategoryTheory.Functor.map_comp]
    exact R.comparison_fac S
  simpa only [criterionPerfHomComparison, Category.assoc, eHomWhiskerRight_comp] using
    (moduleHomPrecomposeHomotopy A E h.some (criterionPerfColumn A D E P d')).compLeft
      (P.toFunctor.map d d')

/-- 全次数の擬同型条件は、源の列の射影解像度の選択に依存しない。 -/
lemma criterionPerfHomComparison_resolution_iff (d d' : D)
    (R S : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    QuasiIso (criterionPerfHomComparison A D E P d d' R) ↔
      QuasiIso (criterionPerfHomComparison A D E P d d' S) := by
  let s := eHomWhiskerRight (Complex A) (R.comparison S) (criterionPerfColumn A D E P d')
  have : QuasiIso s := moduleHomotopicallyProjective_precompose_quasiIso A E
    R.projective S.projective (R.comparison S) (R.comparison_quasiIso S) _
  have h : QuasiIso (criterionPerfHomComparison A D E P d d' S ≫ s) ↔
      QuasiIso (criterionPerfHomComparison A D E P d d' R) := by
    simp only [quasiIso_iff, quasiIsoAt_iff_isIso_homologyMap]
    exact forall_congr' (fun n => by
      rw [(criterionPerfHomComparison_resolution_homotopy A D E P d d' R S).homologyMap_eq n])
  exact h.symm.trans (quasiIso_iff_comp_right _ s)

lemma criterionPerfFullHomQuasiIso_iff (R : ∀ d : D,
    ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    criterionPerfFullHomQuasiIso A D E P ↔
      ∀ d d' : D, QuasiIso (criterionPerfHomComparison A D E P d d' (R d)) := by
  apply forall₂_congr
  intro d d'
  exact criterionPerfHomComparison_resolution_iff A D E P d d' _ _

/-- 列が既に射影的な場合に限り、通常の左作用との比較へ簡約できる。 -/
lemma criterionPerfHomComparison_projective_iff (d d' : D)
    (h : moduleHomotopicallyProjective A E (criterionPerfColumn A D E P d)) :
    QuasiIso (criterionPerfHomComparison A D E P d d'
      (moduleCanonicalProjectiveResolution A E (criterionPerfColumn A D E P d))) ↔
      QuasiIso (P.toFunctor.map d d') := by
  rw [criterionPerfHomComparison_resolution_iff A D E P d d' _
    (moduleIdentityProjectiveResolution A E (criterionPerfColumn A D E P d) h)]
  simp only [criterionPerfHomComparison, moduleIdentityProjectiveResolution,
    eHomWhiskerRight_id]
  change QuasiIso (P.toFunctor.map d d' ≫ 𝟙 _) ↔ _
  rw [Category.comp_id]

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerfHomComparison

/-! ## CriterionPerfHomComparisonZero（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerfHomComparisonZero.lean） -/

/-! # 全 Hom 比較の閉次数零での実際の射の公式 -/

@[expose] public section CriterionPerfHomComparisonZero
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 前合成の複体射は閉次数零でも実際の前合成を与える。 -/
lemma criterionPerf_closedHomEquiv_precompose
    (C : Type v) [DGCategory A C] {x y z : ClosedCategory A C}
    (f : x ⟶ y) (g : y ⟶ z) :
    complexMapZeroCycle A (eHomWhiskerRight (Complex A) f z)
      (closedHomEquiv A C y z g) = closedHomEquiv A C x z (f ≫ g) := by
  have h : eHomEquiv (Complex A) g ≫ eHomWhiskerRight (Complex A) f z =
      eHomEquiv (Complex A) (f ≫ g) := by
    rw [eHomWhiskerRight, eHomEquiv_comp, ← Category.assoc, leftUnitor_inv_naturality]
    simp only [Category.assoc, tensorHom_def']
  apply Subtype.ext
  exact congrArg (fun k => (cycleFromUnit _ k).val) h

/-- dg 関手の全 Hom 射の閉次数零制限は、その通常関手の射写像。 -/
lemma criterionPerf_closedHomEquiv_map
    {C : Type v} [DGCategory A C] {B : Type w} [DGCategory A B]
    (F : DGFunctor A C B) {x y : ClosedCategory A C} (f : x ⟶ y) :
    complexMapZeroCycle A (F.map x y) (closedHomEquiv A C x y f) =
      closedHomEquiv A B (F.onClosed.obj x) (F.onClosed.obj y) (F.onClosed.map f) := by
  apply Subtype.ext
  exact (cycleFromUnit_postcomp _ _).symm

variable (D : Type v) [DGCategory A D] (E : Type w) [DGCategory A E] [Small.{u} E]
  (P : Bimodule A E D)

/-- 全 Hom 比較は増強と kernel の左作用の実際の合成を与える。 -/
lemma criterionPerfHomComparison_closedCycle {d d' : ClosedCategory A D} (f : d ⟶ d')
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    complexMapZeroCycle A (criterionPerfHomComparison A D E P d d' R)
      (closedHomEquiv A D d d' f) =
      closedHomEquiv A (RightModule A E) R.obj (criterionPerfColumn A D E P d')
        (R.π ≫ P.toFunctor.onClosed.map f) := by
  change complexMapZeroCycle A (eHomWhiskerRight (Complex A) R.π _)
    (complexMapZeroCycle A (P.toFunctor.map d d') (closedHomEquiv A D d d' f)) = _
  rw [criterionPerf_closedHomEquiv_map]
  exact criterionPerf_closedHomEquiv_precompose A (RightModule A E) R.π
    (P.toFunctor.onClosed.map f)

/-- 列の導来射を計算する同値の下で、比較の H⁰ 写像は実際の左作用の局所化。 -/
lemma criterionPerfHomComparison_homology_zero {d d' : ClosedCategory A D} (f : d ⟶ d')
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    criterionPerfColumnDerivedHomEquiv A D E P d d' R
        ((moduleToDerived A E).map (P.toFunctor.onClosed.map f)) =
      homologyMap (criterionPerfHomComparison A D E P d d' R) 0
        (complexZeroHomologyClass A (homObject A D d d') (closedHomEquiv A D d d' f)) := by
  rw [complexZeroHomologyClass_naturality, criterionPerfHomComparison_closedCycle]
  change moduleProjectiveDerivedHomologyEquiv A E R.projective _
    ((moduleToDerived A E).map R.π ≫ (moduleToDerived A E).map (P.toFunctor.onClosed.map f)) = _
  rw [← CategoryTheory.Functor.map_comp, moduleProjectiveDerivedHomologyEquiv_map]
  rfl

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerfHomComparisonZero

/-! ## CriterionPerfConditions（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerfConditions.lean） -/

/-! # 主 kernel の Perf 判定の三つの独立した条件

第二条件は通常代表とその主 kernel への同型を持つ存在命題とする。
比較そのものは源の列を射影置換した全 Hom 複体の射である。
-/

@[expose] public section CriterionPerfConditions
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 全 Hom の擬同型比較を持つ通常代表が存在するという、主 kernel 上の条件。 -/
def criterionPerfKernelFullHomQuasiIso (K : Kernel A D E) : Prop :=
  ∃ P : BimoduleCategory A E D,
    Nonempty ((bimoduleToDerived A E D).obj P ≅ K) ∧
      criterionPerfFullHomQuasiIso A D E (BimoduleCategory.underlying A E D P)

/-- 通常代表から主 kernel の第二条件を与える。 -/
lemma criterionPerfKernelFullHomQuasiIso_of_model
    (P : BimoduleCategory A E D) (K : Kernel A D E)
    (e : (bimoduleToDerived A E D).obj P ≅ K)
    (h : criterionPerfFullHomQuasiIso A D E (BimoduleCategory.underlying A E D P)) :
    criterionPerfKernelFullHomQuasiIso A D E K := ⟨P, ⟨e⟩, h⟩

/-- 第二条件は主 kernel の同型で移送でき、代表の選択を構造に固定しない。 -/
lemma criterionPerfKernelFullHomQuasiIso_iso_iff {K L : Kernel A D E} (e : K ≅ L) :
    criterionPerfKernelFullHomQuasiIso A D E K ↔
      criterionPerfKernelFullHomQuasiIso A D E L := by
  constructor
  · rintro ⟨P, ⟨i⟩, h⟩
    exact ⟨P, ⟨i ≪≫ e⟩, h⟩
  · rintro ⟨P, ⟨i⟩, h⟩
    exact ⟨P, ⟨i ≪≫ e.symm⟩, h⟩

/-- 列の perfect 性、全 Hom 複体比較、厚い生成性を独立に保持する。 -/
structure CriterionPerfConditions (K : Kernel A D E) : Prop where
  columnsPerfect : kernelColumnsPerfect A D E K
  fullHomQuasiIso : criterionPerfKernelFullHomQuasiIso A D E K
  columnsThickGenerate : criterionPerfColumnsThickGenerate A D E K

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerfConditions

/-! ## CriterionPerfFullyFaithful（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerfFullyFaithful.lean） -/

/-! # 表現可能対象から Perf への二変数の厚い帰納

全 Hom 複体の条件からここへの橋は別途示す。このファイルでは、全整数 shift の
表現可能対象間で得た射の全単射性を厚い帰納で延長する。
-/

@[expose] public section CriterionPerfFullyFaithful
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Opposite
open scoped CategoryTheory.Pretriangulated.Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

abbrev criterionPerfRepresentable (d : D) : DerivedModuleCategory A D :=
  (moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))

/-- 両変数で shift した表現可能対象上の比較から、両変数の厚い帰納を行う。 -/
lemma criterionPerf_hom_bijective_of_representables
    (F : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    [F.CommShift ℤ] [F.IsTriangulated] [F.Additive]
    (hgen : ∀ (d d' : D) (m n : ℤ), Function.Bijective
      (F.map (X := (criterionPerfRepresentable A D d)⟦m⟧)
        (Y := (criterionPerfRepresentable A D d')⟦n⟧)))
    (X : DerivedModuleCategory A D) (hX : modulePerfect A D X)
    (Y : DerivedModuleCategory A D) (hY : modulePerfect A D Y) :
    Function.Bijective (F.map (X := X) (Y := Y)) := by
  let S₀ : ObjectProperty (DerivedModuleCategory A D) :=
    fun Z => ∃ d : D, Z = criterionPerfRepresentable A D d
  let S := S₀.shiftClosure ℤ
  let P := criterionPerfRelativeHomTargets F S
  have htarget : modulePerfect A D ≤ P := by
    apply (modulePerfect_le_iff_generators A D P).2
    intro d' Z hZ
    obtain ⟨Z', m, e, d, rfl⟩ := hZ
    exact homComparison_bijective_of_iso F e.symm
      ((shiftFunctorZero (DerivedModuleCategory A D) ℤ).app _)
      (hgen d d' m 0)
  let Q := criterionPerfRelativeHomTargets F.op (modulePerfect A D).op
  let : Q.unop.IsStableUnderRetracts := ⟨fun a ha =>
    Q.prop_of_retract a.op ha⟩
  have hsource : modulePerfect A D ≤ Q.unop := by
    apply (modulePerfect_le_iff_generators A D Q.unop).2
    intro d Z hZ
    apply (criterionPerfHomComparison_op_iff F _ _).2
    exact htarget Z.unop hZ _ (S₀.le_shiftClosure _ ⟨d, rfl⟩)
  exact (criterionPerfHomComparison_op_iff F X Y).1 (hsource X hX (op Y) hY)

/-- 実際の kernel 作用の射比較を Perf 制限の充満忠実性へ延長する。
全 Hom 複体条件から `hgen` を導く比較は、この帰納とは分離する。 -/
def criterionPerfFullyFaithfulOfRepresentables (K : Kernel A D E)
    (hK : kernelColumnsPerfect A D E K)
    (hgen : ∀ (d d' : D) (m n : ℤ), Function.Bijective
      ((kernelDerivedTensor A D E K).map (X := (criterionPerfRepresentable A D d)⟦m⟧)
        (Y := (criterionPerfRepresentable A D d')⟦n⟧))) :
    (perfectDerivedKernelAction A D E K hK).FullyFaithful := by
  let := criterionPerfKernelCommShift A D E K
  let := criterionPerfKernelIsTriangulated A D E K
  apply Nonempty.some
  apply (Functor.FullyFaithful.nonempty_iff_map_bijective _).2
  intro X Y
  have h := criterionPerf_hom_bijective_of_representables A D E
    (kernelDerivedTensor A D E K) hgen X.obj X.property Y.obj Y.property
  constructor
  · intro f g he
    apply (modulePerfect A D).hom_ext
    exact h.1 (congrArg (fun k => k.hom) he)
  · intro f
    obtain ⟨g, hg⟩ := h.2 f.hom
    exact ⟨ObjectProperty.homMk g, (modulePerfect A E).hom_ext hg⟩

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerfFullyFaithful

/-! ## CriterionPerfHomComparisonDegrees（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerfHomComparisonDegrees.lean） -/

/-! # 列間の全次数の導来 Hom の計算

源の列だけの射影解像度から、全 Hom 複体の各次数のホモロジーを計算する。
-/

@[expose] public section CriterionPerfHomComparisonDegrees
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- 源の列の s-shift からの導来射は、比較の終域の H^(-s) である。 -/
def criterionPerfColumnDerivedShiftedHomEquiv (d d' : D)
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) (s : ℤ) :
    (((moduleToDerived A E).obj (criterionPerfColumn A D E P d))⟦s⟧ ⟶
        (moduleToDerived A E).obj (criterionPerfColumn A D E P d')) ≃
      (homObject A (RightModule A E) R.obj (criterionPerfColumn A D E P d')).homology (-s) := by
  let Q := moduleToDerived A E
  letI := moduleToDerived_inverts A E R.π R.quasiIso
  let eSource : Q.obj (R.obj⟦s⟧) ≅ (Q.obj (criterionPerfColumn A D E P d))⟦s⟧ :=
    (Q.commShiftIso s).app R.obj ≪≫ (shiftFunctor (DerivedModuleCategory A E) s).mapIso
      (asIso (Q.map R.π))
  let H := moduleHom A E (ForgetEnrichment.to (Complex A) R.obj) (P.rightAt d')
  let eHom := moduleHomSourceShiftIso A E (ForgetEnrichment.to (Complex A) R.obj)
    (P.rightAt d') s
  let eH := homologyMapIso eHom 0 ≪≫
    (CochainComplex.ShiftSequence.shiftIso (ModuleCat A) (-s) 0 (-s) (by omega)).app H
  exact (Iso.homCongr eSource.symm (Iso.refl _)).trans
    ((moduleProjectiveDerivedHomologyEquiv A E
      (moduleHomotopicallyProjective_shift A E R.projective s) _).trans
      eH.toLinearEquiv.toEquiv)

/-- 表現可能対象間の全次数の導来射は、元の dg 圏の全 Hom のホモロジー。 -/
def criterionPerfRepresentableDerivedShiftedHomEquiv [Small.{u} D] (d d' : D) (s : ℤ) :
    ((criterionPerfRepresentable A D d)⟦s⟧ ⟶ criterionPerfRepresentable A D d') ≃
      (homObject A D d d').homology (-s) := by
  let R := moduleIdentityProjectiveResolution A D
    (ForgetEnrichment.of (Complex A) (representable A d))
    (representable_homotopicallyProjective A D d)
  exact (criterionPerfColumnDerivedShiftedHomEquiv A D D (Bimodule.diagonal A D)
    d d' R s).trans
    (homologyMapIso (dgYonedaIso A d (representable A d')) (-s)).toLinearEquiv.toEquiv

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerfHomComparisonDegrees

/-! ## CriterionPerfYonedaAction（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerfYonedaAction.lean） -/

/-! # 表現可能加群上の通常・主導来 kernel 作用の自然な計算 -/

@[expose] public section CriterionPerfYonedaAction
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- Yoneda の後に通常 tensor を適用する dg 関手は、対角との合成そのもの。 -/
lemma criterionPerfYonedaTensor_eq :
    (dgYoneda A D).comp (kernelTensor A D E P) =
      (BimoduleTensor.compose A E D D P (Bimodule.diagonal A D)).toFunctor := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (dgYoneda A D).comp (kernelTensor A D E P))
    (G := (BimoduleTensor.compose A E D D P (Bimodule.diagonal A D)).toFunctor)
    (fun _ => rfl)
  intro d d'
  simp only [eqToHom_refl, Category.comp_id]
  apply moduleHom_ext A E
  intro e
  change ((dgYoneda A D).map d d' ≫ (kernelTensor A D E P).map _ _) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (dgYoneda A D).map d d' ≫ k)
      (kernelTensor_map_π A D E P (representable A d) (representable A d') e)).trans
        (BimoduleTensor.compose_leftMap_π A E D D P (Bimodule.diagonal A D) d d' e).symm)

/-- 対角の右単位を、表現可能対象上の通常 tensor の自然同型にする。 -/
def criterionPerfYonedaTensorIso :
    (dgYoneda A D).onClosed ⋙ (kernelTensor A D E P).onClosed ≅ P.toFunctor.onClosed := by
  let e := eqToIso (congrArg (fun F : DGFunctor A D (RightModule A E) => F.onClosed)
    (criterionPerfYonedaTensor_eq A D E P))
  refine e ≪≫ NatIso.ofComponents (fun d => BimoduleTensor.rightUnitIso A E D P d) ?_
  intro d d' f
  exact (kernelClosedFamilyNatTrans A E D
    (BimoduleTensor.rightBimoduleUnitIso A E D P).hom).naturality f

/-- 表現可能対象上の導来作用の計算は、閉零射にも自然な同型である。 -/
def criterionPerfYonedaDerivedIso :
    (dgYoneda A D).onClosed ⋙ moduleToDerived A D ⋙
        kernelDerivedTensorOnBimodule A D E P ≅ P.toFunctor.onClosed ⋙ moduleToDerived A E := by
  let e : (dgYoneda A D).onClosed ⋙ moduleToDerived A D ⋙
      kernelDerivedTensorOnBimodule A D E P ≅
      (dgYoneda A D).onClosed ⋙ (kernelTensor A D E P).onClosed ⋙ moduleToDerived A E :=
    NatIso.ofComponents
      (fun d => kernelRelativeKFlatComputation A D E P _
        (moduleHomotopicallyProjective_relativeKFlat A D
          (representable_homotopicallyProjective A D d)))
      (fun f => (kernelDerivedTensorAugmentation A D E P).naturality
        ((dgYoneda A D).onClosed.map f))
  exact e ≪≫ isoWhiskerRight (criterionPerfYonedaTensorIso A D E P) (moduleToDerived A E)

/-- 指定主局所化の実際の kernel 関手そのものの、表現可能対象上の自然な計算。 -/
def criterionPerfYonedaMainDerivedIso :
    (dgYoneda A D).onClosed ⋙ moduleToDerived A D ⋙
        kernelDerivedTensor A D E
          ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P)) ≅
      P.toFunctor.onClosed ⋙ moduleToDerived A E :=
  isoWhiskerLeft ((dgYoneda A D).onClosed ⋙ moduleToDerived A D)
    (kernelDerivedTensorOnBimoduleIso A D E (BimoduleCategory.of A E D P)) ≪≫
      criterionPerfYonedaDerivedIso A D E P

/-- 実際の主作用の射を、列の主導来対象間の射として読む。 -/
def criterionPerfYonedaMainActionMap (d d' : ClosedCategory A D)
    (f : criterionPerfRepresentable A D d ⟶ criterionPerfRepresentable A D d') :
    (moduleToDerived A E).obj (criterionPerfColumn A D E P d) ⟶
      (moduleToDerived A E).obj (criterionPerfColumn A D E P d') :=
  (criterionPerfYonedaMainDerivedIso A D E P).inv.app d ≫
    (kernelDerivedTensor A D E
      ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map f ≫
    (criterionPerfYonedaMainDerivedIso A D E P).hom.app d'

/-- 元の dg 圏の閉零射に対して、主作用の射計算は列の左作用の局所化と一致する。 -/
lemma criterionPerfYonedaMainActionMap_closed {d d' : ClosedCategory A D} (f : d ⟶ d') :
    criterionPerfYonedaMainActionMap A D E P d d'
        ((moduleToDerived A D).map ((dgYoneda A D).onClosed.map f)) =
      (moduleToDerived A E).map (P.toFunctor.onClosed.map f) := by
  have h := (criterionPerfYonedaMainDerivedIso A D E P).hom.naturality f
  change _ ≫ (criterionPerfYonedaMainDerivedIso A D E P).hom.app d' =
    (criterionPerfYonedaMainDerivedIso A D E P).hom.app d ≫
      (moduleToDerived A E).map (P.toFunctor.onClosed.map f) at h
  exact (congrArg (fun k => (criterionPerfYonedaMainDerivedIso A D E P).inv.app d ≫ k) h).trans
    (Iso.inv_hom_id_app_assoc _ _ _)

/-- 閉零射の全 Hom 比較の H⁰ は、実際の主 kernel 作用の射写像である。 -/
lemma criterionPerfYonedaMainActionMap_homology_zero {d d' : ClosedCategory A D}
    (f : d ⟶ d') (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    criterionPerfColumnDerivedHomEquiv A D E P d d' R
        (criterionPerfYonedaMainActionMap A D E P d d'
          ((moduleToDerived A D).map ((dgYoneda A D).onClosed.map f))) =
      HomologicalComplex.homologyMap (criterionPerfHomComparison A D E P d d' R) 0
        (complexZeroHomologyClass A (homObject A D d d') (closedHomEquiv A D d d' f)) := by
  rw [criterionPerfYonedaMainActionMap_closed]
  exact criterionPerfHomComparison_homology_zero A D E P f R

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerfYonedaAction

/-! ## CriterionPerfYonedaHomology（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerfYonedaHomology.lean） -/

/-! # 全ての表現可能対象間の導来射に対する H⁰ 比較 -/

@[expose] public section CriterionPerfYonedaHomology
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- dg Yoneda の閉次数零制限は、表現可能加群間の全ての閉零射を与える。 -/
lemma criterionPerfYonedaClosed_map_surjective (d d' : ClosedCategory A D) :
    Function.Surjective ((dgYoneda A D).onClosed.map (X := d) (Y := d')) := by
  intro g
  let c := complexMapZeroCycle A (dgYonedaIso A (D := D) d (representable A (D := D) d')).hom
    (closedHomEquiv A (RightModule A D) _ _ g)
  refine ⟨(closedHomEquiv A D d d').symm c, ?_⟩
  apply (closedHomEquiv A (RightModule A D) _ _).injective
  rw [← criterionPerf_closedHomEquiv_map, Equiv.apply_symm_apply]
  apply Subtype.ext
  change (dgYonedaIso A (D := D) d (representable A (D := D) d')).inv.f 0
    ((dgYonedaIso A (D := D) d (representable A (D := D) d')).hom.f 0
      (closedHomEquiv A (RightModule A D) _ _ g).val) = _
  rw [← ModuleCat.comp_apply, ← comp_f, Iso.hom_inv_id, id_f, ModuleCat.id_apply]

/-- 表現可能対象間の導来射は、元の dg 圏の閉零射の Yoneda 像で表せる。 -/
lemma criterionPerfYonedaDerived_map_surjective (d d' : ClosedCategory A D) :
    Function.Surjective (fun f : d ⟶ d' =>
      (moduleToDerived A D).map ((dgYoneda A D).onClosed.map f)) := by
  intro f
  obtain ⟨g, hg⟩ := (moduleProjectiveDerivedHomEquiv A D
    (representable_homotopicallyProjective A D d) _).surjective f
  obtain ⟨g, rfl⟩ := (moduleToHomotopy A D).map_surjective g
  obtain ⟨g, rfl⟩ := criterionPerfYonedaClosed_map_surjective A D d d' g
  rw [moduleProjectiveDerivedHomEquiv_map] at hg
  exact ⟨g, hg⟩

/-- 実際の Yoneda 射を、元の全 Hom 複体の H⁰ 類に送る公式。 -/
lemma criterionPerfYonedaDerivedHomology_closed {d d' : ClosedCategory A D} (f : d ⟶ d') :
    moduleRepresentableDerivedHomologyEquiv A D d _
        ((moduleToDerived A D).map ((dgYoneda A D).onClosed.map f)) =
      complexZeroHomologyClass A (homObject A D d d') (closedHomEquiv A D d d' f) := by
  rw [moduleRepresentableDerivedHomologyEquiv_map, complexZeroHomologyClass_naturality]
  congr 1
  erw [← criterionPerf_closedHomEquiv_map A (dgYoneda A D) f]
  apply Subtype.ext
  change (dgYonedaIso A (D := D) d (representable A (D := D) d')).hom.f 0
    ((dgYonedaIso A (D := D) d (representable A (D := D) d')).inv.f 0
      (closedHomEquiv A D d d' f).val) = _
  rw [← ModuleCat.comp_apply, ← comp_f, Iso.inv_hom_id, id_f, ModuleCat.id_apply]

variable (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- 閉零代表を指定しない任意の導来射についての、実際の主作用と H⁰ 比較の可換式。 -/
lemma criterionPerfYonedaMainActionMap_homology_zero_all
    (d d' : ClosedCategory A D)
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d))
    (f : criterionPerfRepresentable A D d ⟶ criterionPerfRepresentable A D d') :
    criterionPerfColumnDerivedHomEquiv A D E P d d' R
        (criterionPerfYonedaMainActionMap A D E P d d' f) =
      homologyMap (criterionPerfHomComparison A D E P d d' R) 0
        (moduleRepresentableDerivedHomologyEquiv A D d _ f) := by
  obtain ⟨f, rfl⟩ := criterionPerfYonedaDerived_map_surjective A D d d' f
  dsimp only
  erw [criterionPerfYonedaDerivedHomology_closed A D f]
  exact criterionPerfYonedaMainActionMap_homology_zero A D E P f R

/-- 全 Hom 比較の次数零での擬同型性と、主作用の実際の射写像の全単射性との同値。
これは全次数の擬同型条件の次数零の部分である。 -/
lemma criterionPerfHomComparison_quasiIsoAt_zero_iff
    (d d' : ClosedCategory A D)
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    QuasiIsoAt (criterionPerfHomComparison A D E P d d' R) 0 ↔
      Function.Bijective
        ((kernelDerivedTensor A D E
          ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map
          (X := criterionPerfRepresentable A D d) (Y := criterionPerfRepresentable A D d')) := by
  let eS := moduleRepresentableDerivedHomologyEquiv A D d
    (ForgetEnrichment.of (Complex A) (representable A (D := D) d'))
  let eT := criterionPerfColumnDerivedHomEquiv A D E P d d' R
  let t := criterionPerfYonedaMainActionMap A D E P d d'
  let a := homologyMap (criterionPerfHomComparison A D E P d d' R) 0
  have heq : eT ∘ t = a ∘ eS := funext
    (criterionPerfYonedaMainActionMap_homology_zero_all A D E P d d' R)
  have ht : Function.Bijective t ↔ Function.Bijective a :=
    (Function.Bijective.of_comp_iff' eT.bijective t).symm.trans (by
      rw [heq]
      exact Function.Bijective.of_comp_iff a eS.bijective)
  have hm : Function.Bijective t ↔ Function.Bijective
      ((kernelDerivedTensor A D E
        ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map
        (X := criterionPerfRepresentable A D d) (Y := criterionPerfRepresentable A D d')) :=
    Function.Bijective.of_comp_iff'
      (Iso.homCongr ((criterionPerfYonedaMainDerivedIso A D E P).app d)
        ((criterionPerfYonedaMainDerivedIso A D E P).app d')).bijective _
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  exact ht.symm.trans hm

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerfYonedaHomology

/-! ## CriterionPerfResolvedHomShift（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerfResolvedHomShift.lean） -/

/-! # 射影増強を前合成した全 Hom 比較の shift 計算 -/

@[expose] public section CriterionPerfResolvedHomShift
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- Hom の源 shift の chain 同型の全次数公式。shift の包含との豊穣合成を保つ。 -/
lemma criterionPerfHomSourceShiftIso_apply (M N : RightModule A D) (s q : ℤ)
    (z : (moduleHom A D (shiftModule s M) N).X q) :
    (moduleHomSourceShiftIso A D M N s).hom.f q z =
      forward A (x := M) (y := shiftModule s M) (z := N)
        (moduleShiftInElement A D s M) z (by omega : -s + q = q + -s) := by
  change (complexShiftIsoOfSumZero A _ _ _ _ _ _).hom.f q z = _
  rw [complexShiftIsoOfSumZero_hom, complexShiftComparison_f]
  rfl

/-- shift の包含は閉零加群射と自然に可換する。 -/
lemma criterionPerfModuleShiftIn_naturality (s : ℤ) {M N : ModuleCategory A D}
    (f : M ⟶ N) :
    forward A (x := ForgetEnrichment.to (Complex A) M)
      (y := shiftModule s (ForgetEnrichment.to (Complex A) M))
      (z := shiftModule s (ForgetEnrichment.to (Complex A) N))
      (moduleShiftInElement A D s (ForgetEnrichment.to (Complex A) M))
      (endomorphismClosedElement A D ((moduleShiftFunctor A D s).map f)) (add_zero (-s)) =
    forward A (x := ForgetEnrichment.to (Complex A) M)
      (y := ForgetEnrichment.to (Complex A) N)
      (z := shiftModule s (ForgetEnrichment.to (Complex A) N))
      (endomorphismClosedElement A D f)
      (moduleShiftInElement A D s (ForgetEnrichment.to (Complex A) N)) (zero_add (-s)) := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomForward_π, moduleHomForward_π, moduleShiftInElement_π,
    moduleShiftInElement_π, endomorphismClosedElement_π]
  erw [endomorphismClosedElement_π]
  simp only [mul_zero, zero_mul, Int.negOnePow_zero, one_smul,
    Cochain.units_smul_comp, Cochain.comp_units_smul]
  congr 1
  apply Cochain.ext
  intro i j hij
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v]
  simp only [Cochain.ofHom_v]
  rw [Cochain.rightShift_v _ s (-s) (neg_add_cancel s) i j hij i (add_zero i),
    Cochain.rightShift_v _ s (-s) (neg_add_cancel s) i j hij i (add_zero i)]
  simp only [Cochain.ofHom_v, id_f]
  change (𝟙 _ ≫ _) ≫ ((moduleEvaluation A D x).map (moduleShiftMap A D s f)).f j = _
  rw [moduleShiftMap_eval]
  simp only [Category.id_comp, shiftFunctorObjXIso,
    shiftFunctor_map_f']
  exact (XIsoOfEq_inv_naturality ((moduleEvaluation A D x).map f) (by omega : j + s = i)).symm

/-- 閉零射による Hom の前合成を全次数の豊穣合成として読む。 -/
lemma criterionPerfHomPrecompose_apply {M N T : ModuleCategory A D} (f : M ⟶ N)
    (q : ℤ) (z : (moduleHom A D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) T)).X q) :
    (eHomWhiskerRight (Complex A) f T).f q z =
      forward A (x := ForgetEnrichment.to (Complex A) M)
        (y := ForgetEnrichment.to (Complex A) N) (z := ForgetEnrichment.to (Complex A) T)
        (endomorphismClosedElement A D f) z (zero_add q) := by
  apply moduleHomElement_ext A D
  intro x
  erw [moduleHomWhiskerRight_apply_π, moduleHomForward_π, endomorphismClosedElement_π]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  rfl

/-- 前合成と源 shift の全 Hom chain 同型の可換図式。 -/
lemma criterionPerfHomSourceShiftIso_precompose {M N : ModuleCategory A D}
    (f : M ⟶ N) (T : RightModule A D) (s : ℤ) :
    eHomWhiskerRight (Complex A) ((moduleShiftFunctor A D s).map f)
        (ForgetEnrichment.of (Complex A) T) ≫
      (moduleHomSourceShiftIso A D (ForgetEnrichment.to (Complex A) M) T s).hom =
    (moduleHomSourceShiftIso A D (ForgetEnrichment.to (Complex A) N) T s).hom ≫
      (CategoryTheory.shiftFunctor (Complex A) (-s)).map
        (eHomWhiskerRight (Complex A) f (ForgetEnrichment.of (Complex A) T)) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (moduleHomSourceShiftIso A D (ForgetEnrichment.to (Complex A) M) T s).hom.f q
      ((eHomWhiskerRight (Complex A) ((moduleShiftFunctor A D s).map f)
        (ForgetEnrichment.of (Complex A) T)).f q z) =
    (eHomWhiskerRight (Complex A) f (ForgetEnrichment.of (Complex A) T)).f (q + -s)
      ((moduleHomSourceShiftIso A D (ForgetEnrichment.to (Complex A) N) T s).hom.f q z)
  rw [criterionPerfHomSourceShiftIso_apply, criterionPerfHomSourceShiftIso_apply,
    criterionPerfHomPrecompose_apply]
  erw [criterionPerfHomPrecompose_apply]
  rw [← forward_assoc_of_sum A _ _ _ (add_zero (-s)) (zero_add q) (by omega)]
  rw [criterionPerfModuleShiftIn_naturality]
  exact forward_assoc_of_sum A _ _ _ (zero_add (-s)) (by omega) (by omega)

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerfResolvedHomShift

/-! ## CriterionPerfDGFunctorShift（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerfDGFunctorShift.lean） -/

/-! # dg 関手の像における shift の包含と射影の関係 -/

@[expose] public section CriterionPerfDGFunctorShift
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma criterionPerf_forward_units_smul_right {B : Type w} [DGCategory A B]
    {x y z : B} {p q n : ℤ} (f : GradedHom A x y p) (g : GradedHom A y z q)
    (h : p + q = n) (a : ℤˣ) :
    forward A f (a • g) h = a • forward A f g h := by
  simp only [forward, Units.smul_def, TensorProduct.tmul_smul, map_zsmul]

/-- 正規化射影と包含との合成の符号を、元の shift の単位関係から固定する。 -/
lemma criterionPerfShiftIn_normalizedOut (M : RightModule A D) (s : ℤ) :
    forward A (x := M) (y := shiftModule s M) (z := M)
        (moduleShiftInElement A D s M) (normalizedModuleShiftOut A D s M)
        (neg_add_cancel s) =
      (moduleShiftNormalizationExponent s).negOnePow •
        ((-s * s).negOnePow • (unitElement A M).val) := by
  rw [normalizedModuleShiftOut, criterionPerf_forward_units_smul_right,
    forward_eq_signed_compose, moduleShiftInOut]

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A (RightModule A D) (RightModule A E))

/-- dg 関手は、正規化射影と包含の同じ全次数関係を保存する。 -/
lemma criterionPerfDGFunctor_shiftInOut (M : RightModule A D) (s : ℤ) :
    forward A (x := F.obj M) (y := F.obj (shiftModule s M)) (z := F.obj M)
      ((F.map M (shiftModule s M)).f (-s) (moduleShiftInElement A D s M))
      ((F.map (shiftModule s M) M).f s (normalizedModuleShiftOut A D s M))
      (neg_add_cancel s) =
    forward A (x := F.obj M) (y := shiftModule s (F.obj M)) (z := F.obj M)
      (moduleShiftInElement A E s (F.obj M)) (normalizedModuleShiftOut A E s (F.obj M))
      (neg_add_cancel s) := by
  rw [← F.map_forward A, criterionPerfShiftIn_normalizedOut,
    criterionPerfShiftIn_normalizedOut]
  simp only [Units.smul_def, map_zsmul, F.map_unitElement A]

/-- 正規化 shift 同型は、dg 関手で写した次数 -s の包含を元の包含へ送る。 -/
lemma criterionPerfDGFunctor_shiftIn_hom (M : RightModule A D) (s : ℤ) :
    forward A (x := F.obj M) (y := F.obj (shiftModule s M))
      (z := shiftModule s (F.obj M))
      ((F.map M (shiftModule s M)).f (-s) (moduleShiftInElement A D s M))
      (endomorphismClosedElement A E (normalizedDGModuleFunctorShiftIso A D E F s M).hom)
      (add_zero (-s)) = moduleShiftInElement A E s (F.obj M) := by
  apply moduleHomElement_ext A E
  intro x
  rw [moduleHomForward_π]
  erw [endomorphismClosedElement_π]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  apply Cochain.ext
  intro i j hij
  have hi : i = j + s := by omega
  subst i
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    normalizedDGModuleFunctorShiftIso_hom_eval_f]
  have hc := congrArg (fun z => (moduleHomπ A E (F.obj M) (F.obj M) x).f 0 z)
    (criterionPerfDGFunctor_shiftInOut A D E F M s)
  rw [moduleHomForward_π, moduleHomForward_π] at hc
  have hc' := congrArg (fun z => (-s * s).negOnePow • z) hc
  simp only [smul_smul, Int.units_mul_self, one_smul] at hc'
  have hv := congrArg (fun c => c.v (j + s) (j + s) (add_zero (j + s))) hc'
  rw [Cochain.comp_v _ _ _ (j + s) j (j + s) (by omega) rfl,
    Cochain.comp_v _ _ _ (j + s) j (j + s) (by omega) rfl,
    normalizedModuleShiftOut_v, Category.comp_id] at hv
  exact hv

/-- 逆 shift 比較による前合成は、dg 関手が写した包含を復元する。 -/
lemma criterionPerfDGFunctor_shiftIn_inv (M : RightModule A D) (s : ℤ) :
    forward A (x := F.obj M) (y := shiftModule s (F.obj M))
      (z := F.obj (shiftModule s M))
      (moduleShiftInElement A E s (F.obj M))
      (endomorphismClosedElement A E (normalizedDGModuleFunctorShiftIso A D E F s M).inv)
      (add_zero (-s)) =
    (F.map M (shiftModule s M)).f (-s) (moduleShiftInElement A D s M) := by
  let e := normalizedDGModuleFunctorShiftIso A D E F s M
  apply moduleHomElement_ext A E
  intro x
  rw [moduleHomForward_π]
  erw [endomorphismClosedElement_π]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  apply Cochain.ext
  intro i j hij
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  have h := congrArg (fun z => ((moduleHomπ A E (F.obj M)
    (shiftModule s (F.obj M)) x).f (-s) z).v i j hij)
    (criterionPerfDGFunctor_shiftIn_hom A D E F M s)
  rw [moduleHomForward_π] at h
  erw [endomorphismClosedElement_π] at h
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at h
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at h
  have ht := congrArg (fun k => k ≫ ((moduleEvaluation A E x).map e.inv).f j) h.symm
  rw [Category.assoc, ← comp_f, ← CategoryTheory.Functor.map_comp,
    e.hom_inv_id] at ht
  erw [CategoryTheory.Functor.map_id, id_f, Category.comp_id] at ht
  exact ht

/-- dg 関手の全 Hom 射は、正規化した像の shift と源 shift の chain 比較に両立する。 -/
lemma criterionPerfDGFunctorHom_sourceShift (M N : RightModule A D) (s : ℤ) :
    F.map (shiftModule s M) N ≫
        eHomWhiskerRight (Complex A) (normalizedDGModuleFunctorShiftIso A D E F s M).inv
          (ForgetEnrichment.of (Complex A) (F.obj N)) ≫
        (moduleHomSourceShiftIso A E (F.obj M) (F.obj N) s).hom =
      (moduleHomSourceShiftIso A D M N s).hom ≫
        (CategoryTheory.shiftFunctor (Complex A) (-s)).map (F.map M N) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (moduleHomSourceShiftIso A E (F.obj M) (F.obj N) s).hom.f q
      ((eHomWhiskerRight (Complex A) (normalizedDGModuleFunctorShiftIso A D E F s M).inv
        (ForgetEnrichment.of (Complex A) (F.obj N))).f q ((F.map (shiftModule s M) N).f q z)) =
    (F.map M N).f (q + -s) ((moduleHomSourceShiftIso A D M N s).hom.f q z)
  rw [criterionPerfHomSourceShiftIso_apply, criterionPerfHomSourceShiftIso_apply]
  erw [criterionPerfHomPrecompose_apply]
  rw [← forward_assoc_of_sum A _ _ _ (add_zero (-s)) (zero_add q) (by omega)]
  erw [criterionPerfDGFunctor_shiftIn_inv A D E F M s]
  exact (F.map_forward A _ _ (by omega)).symm

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerfDGFunctorShift

/-! ## CriterionPerfResolvedHom（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerfResolvedHom.lean） -/

/-! # dg 関手の全 Hom 射を、像の源の射影増強により比較する -/

@[expose] public section CriterionPerfResolvedHom
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A (RightModule A D) (RightModule A E))

def criterionPerfResolvedHomComparison (M N : RightModule A D)
    (R : ModuleProjectiveResolution A E (ForgetEnrichment.of (Complex A) (F.obj M))) :
    moduleHom A D M N ⟶
      moduleHom A E (ForgetEnrichment.to (Complex A) R.obj) (F.obj N) :=
  F.map M N ≫ eHomWhiskerRight (Complex A) R.π (ForgetEnrichment.of (Complex A) (F.obj N))

/-- 像の源の解像度を shift し、dg 関手の正規化 shift 同型で増強を戻す。 -/
def criterionPerfDGFunctorShiftResolution (M : RightModule A D)
    (R : ModuleProjectiveResolution A E (ForgetEnrichment.of (Complex A) (F.obj M))) (s : ℤ) :
    ModuleProjectiveResolution A E (ForgetEnrichment.of (Complex A) (F.obj (shiftModule s M))) where
  obj := R.obj⟦s⟧
  π := (moduleShiftFunctor A E s).map R.π ≫
    (normalizedDGModuleFunctorShiftIso A D E F s M).inv
  projective := moduleHomotopicallyProjective_shift A E R.projective s
  quasiIso := by
    intro e
    rw [CategoryTheory.Functor.map_comp]
    have h : QuasiIso ((moduleEvaluation A E e).map ((moduleShiftFunctor A E s).map R.π)) := by
      change QuasiIso ((moduleEvaluation A E e).map (moduleShiftMap A E s R.π))
      rw [moduleShiftMap_eval]
      exact (CochainComplex.quasiIso_shift_iff _ s).2 (R.quasiIso e)
    have := h
    infer_instance

/-- 射影増強後の全 Hom 比較の源 shift 可換図式。 -/
lemma criterionPerfResolvedHomComparison_sourceShift (M N : RightModule A D)
    (R : ModuleProjectiveResolution A E (ForgetEnrichment.of (Complex A) (F.obj M))) (s : ℤ) :
    criterionPerfResolvedHomComparison A D E F (shiftModule s M) N
        (criterionPerfDGFunctorShiftResolution A D E F M R s) ≫
      (moduleHomSourceShiftIso A E (ForgetEnrichment.to (Complex A) R.obj) (F.obj N) s).hom =
    (moduleHomSourceShiftIso A D M N s).hom ≫
      (CategoryTheory.shiftFunctor (Complex A) (-s)).map
        (criterionPerfResolvedHomComparison A D E F M N R) := by
  simp only [criterionPerfResolvedHomComparison, criterionPerfDGFunctorShiftResolution,
    eHomWhiskerRight_comp, Category.assoc]
  rw [criterionPerfHomSourceShiftIso_precompose]
  have h := congrArg (fun k => k ≫ (CategoryTheory.shiftFunctor (Complex A) (-s)).map
    (eHomWhiskerRight (Complex A) R.π (ForgetEnrichment.of (Complex A) (F.obj N))))
    (criterionPerfDGFunctorHom_sourceShift A D E F M N s)
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at h ⊢
  exact h

/-- shift した増強による比較の H⁰ は、元の比較の H^(-s) を検査する。 -/
lemma criterionPerfResolvedHomComparison_shift_zero_iff (M N : RightModule A D)
    (R : ModuleProjectiveResolution A E (ForgetEnrichment.of (Complex A) (F.obj M))) (s : ℤ) :
    QuasiIsoAt (criterionPerfResolvedHomComparison A D E F (shiftModule s M) N
      (criterionPerfDGFunctorShiftResolution A D E F M R s)) 0 ↔
    QuasiIsoAt (criterionPerfResolvedHomComparison A D E F M N R) (-s) := by
  let a := criterionPerfResolvedHomComparison A D E F M N R
  let b := criterionPerfResolvedHomComparison A D E F (shiftModule s M) N
    (criterionPerfDGFunctorShiftResolution A D E F M R s)
  let eT := (moduleHomSourceShiftIso A E (ForgetEnrichment.to (Complex A) R.obj) (F.obj N) s)
  let eS := moduleHomSourceShiftIso A D M N s
  calc
    QuasiIsoAt b 0 ↔ QuasiIsoAt (b ≫ eT.hom) 0 :=
      (quasiIsoAt_iff_comp_right b eT.hom 0).symm
    _ ↔ QuasiIsoAt (eS.hom ≫ (CategoryTheory.shiftFunctor (Complex A) (-s)).map a) 0 := by
      rw [criterionPerfResolvedHomComparison_sourceShift]
    _ ↔ QuasiIsoAt ((CategoryTheory.shiftFunctor (Complex A) (-s)).map a) 0 :=
      quasiIsoAt_iff_comp_left eS.hom _ 0
    _ ↔ QuasiIsoAt a (-s) := CochainComplex.quasiIsoAt_shift_iff a (-s) 0 (-s) (by omega)

/-- 全 Hom の擬同型条件を全ての源 shift の H⁰ 条件として検査できる。 -/
lemma criterionPerfResolvedHomComparison_quasiIso_iff_shifts (M N : RightModule A D)
    (R : ModuleProjectiveResolution A E (ForgetEnrichment.of (Complex A) (F.obj M))) :
    QuasiIso (criterionPerfResolvedHomComparison A D E F M N R) ↔
      ∀ s : ℤ, QuasiIsoAt (criterionPerfResolvedHomComparison A D E F (shiftModule s M) N
        (criterionPerfDGFunctorShiftResolution A D E F M R s)) 0 := by
  constructor
  · intro h s
    apply (criterionPerfResolvedHomComparison_shift_zero_iff A D E F M N R s).2
    exact h.quasiIsoAt (-s)
  · intro h
    rw [quasiIso_iff]
    intro i
    simpa only [neg_neg] using
      (criterionPerfResolvedHomComparison_shift_zero_iff A D E F M N R (-i)).1 (h (-i))

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerfResolvedHom

/-! ## CriterionPerfResolvedAction（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerfResolvedAction.lean） -/

/-! # 射影的入力間の主 kernel 作用と、射影増強後の全 Hom 比較 -/

@[expose] public section CriterionPerfResolvedAction
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

def criterionPerfKernelMainAugmentation :
    moduleToDerived A D ⋙ kernelDerivedTensor A D E
        ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P)) ⟶
      (kernelTensor A D E P).onClosed ⋙ moduleToDerived A E :=
  whiskerLeft (moduleToDerived A D)
      (kernelDerivedTensorOnBimoduleIso A D E (BimoduleCategory.of A E D P)).hom ≫
    kernelDerivedTensorAugmentation A D E P

/-- 射影的入力に対する主作用の計算同型は、自然な増強から取る。 -/
def criterionPerfKernelProjectiveComputation (M : ModuleCategory A D)
    (hM : moduleHomotopicallyProjective A D M) :
    (kernelDerivedTensor A D E
        ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).obj
        ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj M) := by
  have := kernelDerivedTensorAugmentation_isIso_of_relativeKFlat A D E P M
    (moduleHomotopicallyProjective_relativeKFlat A D hM)
  have : IsIso ((criterionPerfKernelMainAugmentation A D E P).app M) := by
    dsimp only [criterionPerfKernelMainAugmentation, NatTrans.comp_app, whiskerLeft_app]
    infer_instance
  exact asIso ((criterionPerfKernelMainAugmentation A D E P).app M)

def criterionPerfKernelProjectiveActionMap {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : (moduleToDerived A D).obj M ⟶ (moduleToDerived A D).obj N) :
    (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj M) ⟶
      (moduleToDerived A E).obj ((kernelTensor A D E P).onClosed.obj N) :=
  (criterionPerfKernelProjectiveComputation A D E P M hM).inv ≫
    (kernelDerivedTensor A D E
      ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map f ≫
    (criterionPerfKernelProjectiveComputation A D E P N hN).hom

lemma criterionPerfKernelProjectiveActionMap_closed {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) :
    criterionPerfKernelProjectiveActionMap A D E P hM hN ((moduleToDerived A D).map f) =
      (moduleToDerived A E).map ((kernelTensor A D E P).onClosed.map f) := by
  have h := (criterionPerfKernelMainAugmentation A D E P).naturality f
  exact (congrArg
    (fun k => (criterionPerfKernelProjectiveComputation A D E P M hM).inv ≫ k) h).trans
    (Iso.inv_hom_id_assoc (criterionPerfKernelProjectiveComputation A D E P M hM) _)

lemma criterionPerfResolvedAction_homology_zero {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (R : ModuleProjectiveResolution A E ((kernelTensor A D E P).onClosed.obj M))
    (f : (moduleToDerived A D).obj M ⟶ (moduleToDerived A D).obj N) :
    criterionPerfColumnDerivedHomEquiv A (RightModule A D) E (kernelTensor A D E P) M N R
        (criterionPerfKernelProjectiveActionMap A D E P hM hN f) =
      homologyMap (criterionPerfResolvedHomComparison A D E (kernelTensor A D E P) M N R) 0
        (moduleProjectiveDerivedHomologyEquiv A D hM N f) := by
  obtain ⟨g, hg⟩ := (moduleProjectiveDerivedHomEquiv A D hM N).surjective f
  obtain ⟨g, rfl⟩ := (moduleToHomotopy A D).map_surjective g
  rw [moduleProjectiveDerivedHomEquiv_map] at hg
  subst f
  rw [criterionPerfKernelProjectiveActionMap_closed, moduleProjectiveDerivedHomologyEquiv_map]
  exact criterionPerfHomComparison_homology_zero A (RightModule A D) E
    (kernelTensor A D E P) g R

lemma criterionPerfResolvedAction_quasiIsoAt_zero_iff {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (R : ModuleProjectiveResolution A E ((kernelTensor A D E P).onClosed.obj M)) :
    QuasiIsoAt (criterionPerfResolvedHomComparison A D E (kernelTensor A D E P) M N R) 0 ↔
      Function.Bijective
        ((kernelDerivedTensor A D E
          ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map
          (X := (moduleToDerived A D).obj M) (Y := (moduleToDerived A D).obj N)) := by
  let eS := moduleProjectiveDerivedHomologyEquiv A D hM N
  let eT := criterionPerfColumnDerivedHomEquiv A (RightModule A D) E
    (kernelTensor A D E P) M N R
  let t := criterionPerfKernelProjectiveActionMap A D E P hM hN
  let a := homologyMap (criterionPerfResolvedHomComparison A D E (kernelTensor A D E P) M N R) 0
  have heq : eT ∘ t = a ∘ eS := funext (criterionPerfResolvedAction_homology_zero A D E P hM hN R)
  have ht : Function.Bijective t ↔ Function.Bijective a :=
    (Function.Bijective.of_comp_iff' eT.bijective t).symm.trans (by
      rw [heq]
      exact Function.Bijective.of_comp_iff a eS.bijective)
  have hm : Function.Bijective t ↔ Function.Bijective
      ((kernelDerivedTensor A D E
        ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map
        (X := (moduleToDerived A D).obj M) (Y := (moduleToDerived A D).obj N)) :=
    Function.Bijective.of_comp_iff'
      (Iso.homCongr (criterionPerfKernelProjectiveComputation A D E P M hM)
        (criterionPerfKernelProjectiveComputation A D E P N hN)).bijective _
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  exact ht.symm.trans hm

/-- 全 Hom 比較の擬同型性は、全ての源 shift 上での主作用の射の全単射性に一致する。 -/
lemma criterionPerfResolvedAction_quasiIso_iff_sourceShifts {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (R : ModuleProjectiveResolution A E ((kernelTensor A D E P).onClosed.obj M)) :
    QuasiIso (criterionPerfResolvedHomComparison A D E (kernelTensor A D E P) M N R) ↔
      ∀ s : ℤ, Function.Bijective
        ((kernelDerivedTensor A D E
          ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map
          (X := (moduleToDerived A D).obj (M⟦s⟧)) (Y := (moduleToDerived A D).obj N)) := by
  rw [criterionPerfResolvedHomComparison_quasiIso_iff_shifts]
  apply forall_congr'
  intro s
  exact criterionPerfResolvedAction_quasiIsoAt_zero_iff A D E P
    (moduleHomotopicallyProjective_shift A D hM s) hN _

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerfResolvedAction

/-! ## CriterionPerfTensorHomComparison（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerfTensorHomComparison.lean） -/

/-! # 列の全 Hom 比較と、表現可能入力の tensor の全 Hom 比較の同定 -/

@[expose] public section CriterionPerfTensorHomComparison
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

private lemma homComparison_resolution_square
    {B : Type*} [Category* B] [EnrichedOrdinaryCategory (Complex A) B]
    {U U' V V' T : B} {H : Complex A}
    (f : H ⟶ (U ⟶[Complex A] U')) (g : H ⟶ (V ⟶[Complex A] V'))
    (e : U ≅ V) (e' : U' ≅ V')
    (h : f ≫ eHomWhiskerLeft (Complex A) U e'.hom =
      g ≫ eHomWhiskerRight (Complex A) e.hom V') (r : T ⟶ V) :
    f ≫ eHomWhiskerRight (Complex A) (r ≫ e.inv) U' ≫
        eHomWhiskerLeft (Complex A) T e'.hom =
      g ≫ eHomWhiskerRight (Complex A) r V' := by
  simp only [eHomWhiskerRight_comp, Category.assoc]
  rw [← eHom_whisker_exchange, ← eHom_whisker_exchange_assoc]
  rw [reassoc_of% h, ← eHomWhiskerRight_comp_assoc, e.inv_hom_id,
    eHomWhiskerRight_id, Category.id_comp]

def criterionPerfTensorRepresentableResolution (d : D)
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    ModuleProjectiveResolution A E
      ((kernelTensor A D E P).onClosed.obj
        (ForgetEnrichment.of (Complex A) (representable A d))) where
  obj := R.obj
  π := R.π ≫ (BimoduleTensor.rightUnitIso A E D P d).inv
  projective := R.projective
  quasiIso := by
    intro e
    rw [CategoryTheory.Functor.map_comp]
    have := R.quasiIso e
    infer_instance

lemma criterionPerfTensorYonedaHom_naturality (d d' : D) :
    yonedaHom A D d d' ≫ (kernelTensor A D E P).map (representable A d) (representable A d') ≫
      eHomWhiskerLeft (Complex A)
        (ForgetEnrichment.of (Complex A) ((kernelTensor A D E P).obj (representable A d)))
        (BimoduleTensor.rightUnitIso A E D P d').hom =
    P.toFunctor.map d d' ≫ eHomWhiskerRight (Complex A)
      (BimoduleTensor.rightUnitIso A E D P d).hom (criterionPerfColumn A D E P d') := by
  have h := BimoduleTensor.rightUnitIso_naturality A E D P d d'
  have he : yonedaHom A D d d' ≫
      (kernelTensor A D E P).map (representable A d) (representable A d') =
      (BimoduleTensor.compose A E D D P (Bimodule.diagonal A D)).toFunctor.map d d' := by
    apply moduleHom_ext A E
    intro e
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => yonedaHom A D d d' ≫ k)
        (kernelTensor_map_π A D E P (representable A d) (representable A d') e)).trans
          (BimoduleTensor.compose_leftMap_π A E D D P (Bimodule.diagonal A D) d d' e).symm)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ eHomWhiskerLeft (Complex A)
      (ForgetEnrichment.of (Complex A) ((kernelTensor A D E P).obj (representable A d)))
      (BimoduleTensor.rightUnitIso A E D P d').hom) he).trans h)

lemma criterionPerfTensorHomComparison_square (d d' : D)
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    yonedaHom A D d d' ≫
        criterionPerfResolvedHomComparison A D E (kernelTensor A D E P)
          (representable A d) (representable A d')
          (criterionPerfTensorRepresentableResolution A D E P d R) ≫
        eHomWhiskerLeft (Complex A) R.obj (BimoduleTensor.rightUnitIso A E D P d').hom =
      criterionPerfHomComparison A D E P d d' R := by
  have h := homComparison_resolution_square A
    (yonedaHom A D d d' ≫ (kernelTensor A D E P).map (representable A d) (representable A d'))
    (P.toFunctor.map d d') (BimoduleTensor.rightUnitIso A E D P d)
    (BimoduleTensor.rightUnitIso A E D P d')
    (by
      have h0 := criterionPerfTensorYonedaHom_naturality A D E P d d'
      simp only [Category.assoc] at h0 ⊢
      exact h0) R.π
  simp only [criterionPerfResolvedHomComparison, criterionPerfTensorRepresentableResolution,
    criterionPerfHomComparison, Category.assoc] at h ⊢
  exact h

lemma criterionPerfTensorHomComparison_quasiIso_iff (d d' : D)
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    QuasiIso (criterionPerfHomComparison A D E P d d' R) ↔
      QuasiIso (criterionPerfResolvedHomComparison A D E (kernelTensor A D E P)
        (representable A d) (representable A d')
        (criterionPerfTensorRepresentableResolution A D E P d R)) := by
  have : QuasiIso (yonedaHom A D d d') := by
    change QuasiIso (dgYonedaIso A d (representable A d')).inv
    infer_instance
  let p := eHomWhiskerLeft (Complex A) R.obj (BimoduleTensor.rightUnitIso A E D P d').hom
  have : IsIso p := by
    change IsIso (((eHomFunctor (Complex A) (ModuleCategory A E)).obj (Opposite.op R.obj)).map
      (BimoduleTensor.rightUnitIso A E D P d').hom)
    infer_instance
  rw [← criterionPerfTensorHomComparison_square A D E P d d' R]
  exact (quasiIso_iff_comp_left (yonedaHom A D d d') (_ ≫ p)).trans
    (quasiIso_iff_comp_right _ p)

/-- 元の列の全 Hom 比較は、表現可能入力の全源 shift 上の主作用で検査できる。 -/
lemma criterionPerfHomComparison_quasiIso_iff_sourceShifts (d d' : D)
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    QuasiIso (criterionPerfHomComparison A D E P d d' R) ↔
      ∀ s : ℤ, Function.Bijective
        ((kernelDerivedTensor A D E
          ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map
          (X := (moduleToDerived A D).obj
            ((ForgetEnrichment.of (Complex A) (representable A d))⟦s⟧))
          (Y := criterionPerfRepresentable A D d')) :=
  (criterionPerfTensorHomComparison_quasiIso_iff A D E P d d' R).trans
    (criterionPerfResolvedAction_quasiIso_iff_sourceShifts A D E P
      (representable_homotopicallyProjective A D d)
      (representable_homotopicallyProjective A D d')
      (criterionPerfTensorRepresentableResolution A D E P d R))

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerfTensorHomComparison

/-! ## CriterionPerfFullHomCriterion（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerfFullHomCriterion.lean） -/

/-! # 全 Hom 複体の条件と、実際の主作用の全整数 shift 上の射比較 -/

@[expose] public section CriterionPerfFullHomCriterion
universe u v w u₁ u₂ v₁ v₂

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory

private lemma map_bijective_natIso_iff
    {C : Type u₁} [Category.{v₁} C] {B : Type u₂} [Category.{v₂} B]
    {F G : C ⥤ B} (e : F ≅ G) (X Y : C) :
    Function.Bijective (F.map (X := X) (Y := Y)) ↔
      Function.Bijective (G.map (X := X) (Y := Y)) := by
  have heq : (Iso.homCongr (e.app X) (e.app Y)) ∘ F.map = G.map := by
    funext f
    exact (congrArg (fun k => e.inv.app X ≫ k) (e.hom.naturality f)).trans
      (e.inv_hom_id_app_assoc X _)
  rw [← heq]
  exact (Function.Bijective.of_comp_iff' (Iso.homCongr (e.app X) (e.app Y)).bijective _).symm

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- 全 Hom 条件を通常の射集合に置き換えず、その全次数の計算から全 shift の射比較を得る。 -/
lemma criterionPerfFullHomQuasiIso_iff_representableMaps :
    criterionPerfFullHomQuasiIso A D E P ↔
      ∀ (d d' : D) (m n : ℤ), Function.Bijective
        ((kernelDerivedTensor A D E
          ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map
          (X := (criterionPerfRepresentable A D d)⟦m⟧)
          (Y := (criterionPerfRepresentable A D d')⟦n⟧)) := by
  let K := (bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P)
  let F := kernelDerivedTensor A D E K
  let := criterionPerfKernelCommShift A D E K
  constructor
  · intro h
    have hs (d d' : D) (s : ℤ) : Function.Bijective
        (F.map (X := (criterionPerfRepresentable A D d)⟦s⟧)
          (Y := criterionPerfRepresentable A D d')) := by
      have hb := (criterionPerfHomComparison_quasiIso_iff_sourceShifts A D E P d d'
        (moduleCanonicalProjectiveResolution A E (criterionPerfColumn A D E P d))).1 (h d d') s
      exact homComparison_bijective_of_iso F
        (((moduleToDerived A D).commShiftIso s).app
          (ForgetEnrichment.of (Complex A) (representable A d))) (Iso.refl _) hb
    intro d d' m n
    exact homComparison_bijective_of_iso F
      ((shiftFunctorAdd' (DerivedModuleCategory A D) (m - n) n m (by omega)).symm.app _)
      (Iso.refl _) (homComparison_bijective_shift_both F (hs d d' (m - n)) n)
  · intro h d d'
    apply (criterionPerfHomComparison_quasiIso_iff_sourceShifts A D E P d d'
      (moduleCanonicalProjectiveResolution A E (criterionPerfColumn A D E P d))).2
    intro s
    exact homComparison_bijective_of_iso F
      (((moduleToDerived A D).commShiftIso s).app
        (ForgetEnrichment.of (Complex A) (representable A d))).symm
      ((shiftFunctorZero (DerivedModuleCategory A D) ℤ).app _) (h d d' s 0)

/-- 代表の存在で定式化した主 kernel の全 Hom 条件と、実際の作用の全 shift の比較。 -/
lemma criterionPerfKernelFullHomQuasiIso_iff_representableMaps (K : Kernel A D E) :
    criterionPerfKernelFullHomQuasiIso A D E K ↔
      ∀ (d d' : D) (m n : ℤ), Function.Bijective
        ((kernelDerivedTensor A D E K).map
          (X := (criterionPerfRepresentable A D d)⟦m⟧)
          (Y := (criterionPerfRepresentable A D d')⟦n⟧)) := by
  constructor
  · rintro ⟨P, ⟨e⟩, h⟩ d d' m n
    exact (map_bijective_natIso_iff ((kernelDerivedTensorFunctor A D E).mapIso e) _ _).1
      ((criterionPerfFullHomQuasiIso_iff_representableMaps A D E
        (BimoduleCategory.underlying A E D P)).1 h d d' m n)
  · intro h
    obtain ⟨⟨P⟩⟩ := K
    refine ⟨P, ⟨Iso.refl _⟩, ?_⟩
    exact (criterionPerfFullHomQuasiIso_iff_representableMaps A D E
      (BimoduleCategory.underlying A E D P)).2 h

/-- 主 kernel の条件は、どの通常代表で全 Hom を計算しても同じ条件となる。 -/
lemma criterionPerfKernelFullHomQuasiIso_model_iff
    (Q : BimoduleCategory A E D) (K : Kernel A D E)
    (e : (bimoduleToDerived A E D).obj Q ≅ K) :
    criterionPerfKernelFullHomQuasiIso A D E K ↔
      criterionPerfFullHomQuasiIso A D E (BimoduleCategory.underlying A E D Q) := by
  constructor
  · intro h
    apply (criterionPerfFullHomQuasiIso_iff_representableMaps A D E _).2
    intro d d' m n
    exact (map_bijective_natIso_iff ((kernelDerivedTensorFunctor A D E).mapIso e) _ _).2
      ((criterionPerfKernelFullHomQuasiIso_iff_representableMaps A D E K).1 h d d' m n)
  · exact criterionPerfKernelFullHomQuasiIso_of_model A D E Q K e

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerfFullHomCriterion
