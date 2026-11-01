module

public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfTriangulated
public import SerrePositivity.DifferentialGraded.Morita.CriterionDerivedCoproducts
public import SerrePositivity.DifferentialGraded.Morita.Perfect
public import SerrePositivity.DifferentialGraded.Verdier.Scalar
public import Mathlib.CategoryTheory.Functor.OfSequence
public import SerrePositivity.DifferentialGraded.Perfect.Compact.FiniteGeneration
public import SerrePositivity.DifferentialGraded.Endomorphism.Derived.Functors

/-!
# Morita.Adjunction.Construction

## 概要
telescope と局所生成による一般 kernel 右随伴の構成・Morita 判定をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## CriterionPerf（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerf.lean） -/

/-! # 一般 kernel の Perf 上の Morita 判定

列の perfect 性、全 Hom 複体の擬同型比較、列の厚い生成性の三条件と、実際の
主導来作用が Perf 上の同値であることの証拠との必要十分条件。一般右随伴を使わない。
-/

@[expose] public section CriterionPerf
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)

/-- 三つの独立した条件から、実際の主作用に一致する Perf 同値を構成する。 -/
def criterionPerfEquivalenceOfConditions (h : CriterionPerfConditions A D E K) :
    CriterionPerfEquivalenceWitness A D E K := by
  let hFF := criterionPerfFullyFaithfulOfRepresentables A D E K h.columnsPerfect
    ((criterionPerfKernelFullHomQuasiIso_iff_representableMaps A D E K).1 h.fullHomQuasiIso)
  let := hFF.full
  let := hFF.faithful
  exact criterionPerfEquivalenceWitnessOfFullyFaithful A D E K
    h.columnsPerfect h.columnsThickGenerate

variable (W : CriterionPerfEquivalenceWitness A D E K)
include W

/-- 実際の Perf 同値の必要条件として、全 Hom 複体の比較は擬同型である。 -/
lemma CriterionPerfEquivalenceWitness.fullHomQuasiIso :
    criterionPerfKernelFullHomQuasiIso A D E K := by
  apply (criterionPerfKernelFullHomQuasiIso_iff_representableMaps A D E K).2
  let := W.actionIsEquivalence A D E K
  let F := perfectDerivedKernelAction A D E K (W.columnsPerfect A D E K)
  intro d d' m n
  let X : PerfectModuleCategory A D :=
    ⟨(criterionPerfRepresentable A D d)⟦m⟧,
      (modulePerfect A D).le_shift m _
        (modulePerfectOver_representable A D d (Set.mem_univ d))⟩
  let Y : PerfectModuleCategory A D :=
    ⟨(criterionPerfRepresentable A D d')⟦n⟧,
      (modulePerfect A D).le_shift n _
        (modulePerfectOver_representable A D d' (Set.mem_univ d'))⟩
  constructor
  · intro f g he
    have h : F.map (ObjectProperty.homMk (X := X) (Y := Y) f) =
        F.map (ObjectProperty.homMk (X := X) (Y := Y) g) :=
      (modulePerfect A E).hom_ext he
    exact congrArg (fun k => k.hom) (F.map_injective h)
  · intro f
    obtain ⟨g, hg⟩ := F.map_surjective (ObjectProperty.homMk (X := F.obj X) (Y := F.obj Y) f)
    exact ⟨g.hom, congrArg (fun k => k.hom) hg⟩

/-- Perf 同値なら、列の perfect 性・全 Hom 複体比較・厚い生成性の三条件が必要。 -/
theorem CriterionPerfEquivalenceWitness.conditions : CriterionPerfConditions A D E K :=
  ⟨W.columnsPerfect A D E K, W.fullHomQuasiIso A D E K, W.columnsThickGenerate A D E K⟩

omit W in
/-- 一般 kernel の Perf Morita 判定。三条件のいずれにも他の二条件を含めない。 -/
theorem criterionPerfMorita_iff :
    CriterionPerfConditions A D E K ↔ Nonempty (CriterionPerfEquivalenceWitness A D E K) :=
  ⟨fun h => ⟨criterionPerfEquivalenceOfConditions A D E K h⟩,
    fun ⟨W⟩ => W.conditions A D E K⟩

omit W in
/-- 列の perfect 性を指定した場合の、実際の Perf 制限についての判定。 -/
theorem criterionPerfAction_isEquivalence_iff (hK : kernelColumnsPerfect A D E K) :
    (perfectDerivedKernelAction A D E K hK).IsEquivalence ↔
      criterionPerfKernelFullHomQuasiIso A D E K ∧ criterionPerfColumnsThickGenerate A D E K := by
  constructor
  · intro h
    let W : CriterionPerfEquivalenceWitness A D E K :=
      ⟨(perfectDerivedKernelAction A D E K hK).asEquivalence,
        (perfectDerivedKernelActionInclusionIso A D E K hK).symm⟩
    exact ⟨W.fullHomQuasiIso A D E K, W.columnsThickGenerate A D E K⟩
  · rintro ⟨hHom, hgen⟩
    let W := criterionPerfEquivalenceOfConditions A D E K ⟨hK, hHom, hgen⟩
    exact W.actionIsEquivalence A D E K

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerf

/-! ## CriterionPerfRelativeFullyFaithful（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerfRelativeFullyFaithful.lean） -/

/-!
概要：指定生成集合の全シフト間の Hom 比較をその thick 閉包へ延長する。
方針：相対 Hom 比較の cone 二対三と retract 閉性で両変数の厚い帰納を行う。
規約：生成集合を入力に保持し、既存の全代表版を変更しない。
使われ方：D-17 の実 dg 関手に対する自由代表からの生成判定。
-/

@[expose] public section CriterionPerfRelativeFullyFaithful
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Opposite
open scoped CategoryTheory.Pretriangulated.Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

lemma criterionPerf_hom_bijective_of_generators
    (F : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    [F.CommShift ℤ] [F.IsTriangulated] [F.Additive] (G : Set D)
    (hgen : ∀ (d : D), d ∈ G → ∀ (d' : D), d' ∈ G → ∀ (m n : ℤ),
      Function.Bijective (F.map (X := (criterionPerfRepresentable A D d)⟦m⟧)
        (Y := (criterionPerfRepresentable A D d')⟦n⟧)))
    (X : DerivedModuleCategory A D) (hX : modulePerfectOver A D G X)
    (Y : DerivedModuleCategory A D) (hY : modulePerfectOver A D G Y) :
    Function.Bijective (F.map (X := X) (Y := Y)) := by
  let S₀ : ObjectProperty (DerivedModuleCategory A D) :=
    fun Z => ∃ d ∈ G, Z = criterionPerfRepresentable A D d
  let S := S₀.shiftClosure ℤ
  let P := criterionPerfRelativeHomTargets F S
  have htarget : modulePerfectOver A D G ≤ P := by
    apply (modulePerfectOver_le_iff_generators A D P G).2
    intro d' hd' Z hZ
    obtain ⟨Z', m, e, d, hd, rfl⟩ := hZ
    exact homComparison_bijective_of_iso F e.symm
      ((shiftFunctorZero (DerivedModuleCategory A D) ℤ).app _)
      (hgen d hd d' hd' m 0)
  let Q := criterionPerfRelativeHomTargets F.op (modulePerfectOver A D G).op
  let : Q.unop.IsStableUnderRetracts := ⟨fun a ha => Q.prop_of_retract a.op ha⟩
  have hsource : modulePerfectOver A D G ≤ Q.unop := by
    apply (modulePerfectOver_le_iff_generators A D Q.unop G).2
    intro d hd Z hZ
    apply (criterionPerfHomComparison_op_iff F _ _).2
    exact htarget Z.unop hZ _ (S₀.le_shiftClosure _ ⟨d, hd, rfl⟩)
  exact (criterionPerfHomComparison_op_iff F X Y).1 (hsource X hX (op Y) hY)

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerfRelativeFullyFaithful

/-! ## CriterionPerfGeneratorHomComparison（旧 SerrePositivity/DifferentialGraded/Morita/CriterionPerfGeneratorHomComparison.lean） -/

/-!
概要：指定生成集合の局所 Hom 複体条件を全 Perf の Hom 比較へ延長する。
方針：同じ kernel の全シフト比較から、両変数の cone 二対三・retract 帰納を適用する。
規約：通常代表の解消比較を保持し、生成条件を H⁰ 充満忠実性に置き換えない。
使われ方：D-17 の graph kernel による元の dg 関手の全 Hom 生成判定。
-/

@[expose] public section CriterionPerfGeneratorHomComparison
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

lemma criterionPerfHomComparison_iff_shiftedRepresentableMaps (d d' : D) :
    QuasiIso (criterionPerfHomComparison A D E P d d'
      (moduleCanonicalProjectiveResolution A E (criterionPerfColumn A D E P d))) ↔
    ∀ (m n : ℤ), Function.Bijective
      ((kernelDerivedTensor A D E
        ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))).map
        (X := (criterionPerfRepresentable A D d)⟦m⟧)
        (Y := (criterionPerfRepresentable A D d')⟦n⟧)) := by
  let K := (bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P)
  let F := kernelDerivedTensor A D E K
  let := criterionPerfKernelCommShift A D E K
  constructor
  · intro h
    have hs (s : ℤ) : Function.Bijective
        (F.map (X := (criterionPerfRepresentable A D d)⟦s⟧)
          (Y := criterionPerfRepresentable A D d')) := by
      have hb := (criterionPerfHomComparison_quasiIso_iff_sourceShifts A D E P d d'
        (moduleCanonicalProjectiveResolution A E (criterionPerfColumn A D E P d))).1 h s
      exact homComparison_bijective_of_iso F
        (((moduleToDerived A D).commShiftIso s).app
          (ForgetEnrichment.of (Complex A) (representable A d))) (Iso.refl _) hb
    intro m n
    exact homComparison_bijective_of_iso F
      ((shiftFunctorAdd' (DerivedModuleCategory A D) (m - n) n m (by omega)).symm.app _)
      (Iso.refl _) (homComparison_bijective_shift_both F (hs (m - n)) n)
  · intro h
    apply (criterionPerfHomComparison_quasiIso_iff_sourceShifts A D E P d d'
      (moduleCanonicalProjectiveResolution A E (criterionPerfColumn A D E P d))).2
    intro s
    exact homComparison_bijective_of_iso F
      (((moduleToDerived A D).commShiftIso s).app
        (ForgetEnrichment.of (Complex A) (representable A d))).symm
      ((shiftFunctorZero (DerivedModuleCategory A D) ℤ).app _) (h s 0)

lemma criterionPerfFullHomQuasiIso_of_generators (G : Set D)
    (hG : modulePerfectOver A D G = modulePerfect A D)
    (h : ∀ d ∈ G, ∀ d' ∈ G,
      QuasiIso (criterionPerfHomComparison A D E P d d'
        (moduleCanonicalProjectiveResolution A E (criterionPerfColumn A D E P d)))) :
    criterionPerfFullHomQuasiIso A D E P := by
  let K := (bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P)
  let F := kernelDerivedTensor A D E K
  let := criterionPerfKernelCommShift A D E K
  let := criterionPerfKernelIsTriangulated A D E K
  apply (criterionPerfFullHomQuasiIso_iff_representableMaps A D E P).2
  intro d d' m n
  apply criterionPerf_hom_bijective_of_generators A D E F G
    (fun x hx y hy => (criterionPerfHomComparison_iff_shiftedRepresentableMaps
      A D E P x y).1 (h x hx y hy))
  · rw [hG]
    exact (modulePerfect A D).le_shift m _ (modulePerfectOver_representable A D d (Set.mem_univ _))
  · rw [hG]
    exact (modulePerfect A D).le_shift n _ (modulePerfectOver_representable A D d' (Set.mem_univ _))

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionPerfGeneratorHomComparison

/-! ## AdjunctionKernelSuccessor（旧 SerrePositivity/DifferentialGraded/Morita/AdjunctionKernelSuccessor.lean） -/

/-! # 実際のkernel作用に対する生成元被覆と関係除去

## 概要
任意の主導来kernelについて、初期被覆と生成元の関係を消す後続操作を構成する。

## 方針
実際の余積保存と既存のshift・三角性を、表現対象の被覆・後続操作へ供給する。

## 規約と注意
局所Hom K-flat性・kernelの列の射影性を追加しない。導来右随伴の存在そのものは後続で証明する。

## 使われ方
U16aの一般右随伴を構成する可算近似列の初期値と後続値に使う。
-/

@[expose] public section AdjunctionKernelSuccessor
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)

/-- 任意の主導来kernelの作用に対する実際の初期被覆射。 -/
def kernelBrownSeedMap (Y : DerivedModuleCategory A E) :
    (kernelDerivedTensor A D E K).obj
        (brownSeed A D E (kernelDerivedTensor A D E K) Y) ⟶ Y := by
  let := kernelDerivedTensorPreservesCoproducts A D E
    (J := brownSeedIndex A D E (kernelDerivedTensor A D E K) Y) K
  exact brownSeedMap A D E (kernelDerivedTensor A D E K) Y

/-- 実際のkernel作用の初期被覆は、生成元の像からの全ての射を表す。 -/
lemma kernelBrownSeedMap_generator_surjective (Y : DerivedModuleCategory A E) (p : D × ℤ)
    (f : (kernelDerivedTensor A D E K).obj (moduleCompactGenerators A D p) ⟶ Y) :
    ∃ g : moduleCompactGenerators A D p ⟶
        brownSeed A D E (kernelDerivedTensor A D E K) Y,
      (kernelDerivedTensor A D E K).map g ≫ kernelBrownSeedMap A D E K Y = f := by
  let := kernelDerivedTensorPreservesCoproducts A D E
    (J := brownSeedIndex A D E (kernelDerivedTensor A D E K) Y) K
  exact brownSeedMap_generator_surjective A D E (kernelDerivedTensor A D E K) Y p f

/-- 任意の主導来kernelについて、生成元の全関係を消す後続操作を選ぶ。 -/
def kernelBrownSuccessor {X : DerivedModuleCategory A D} {Y : DerivedModuleCategory A E}
    (r : (kernelDerivedTensor A D E K).obj X ⟶ Y) :
    BrownSuccessor A D E (kernelDerivedTensor A D E K) r := by
  let := mainKernelActionCommShift A D E K
  let := mainKernelActionIsTriangulated A D E K
  let := kernelDerivedTensorPreservesCoproducts A D E
    (J := brownRelationIndex A D E (kernelDerivedTensor A D E K) r) K
  exact brownSuccessor A D E (kernelDerivedTensor A D E K) r

/-- 実際のkernelの後続操作は、元の標的射を延長する。 -/
lemma kernelBrownSuccessor_fac {X : DerivedModuleCategory A D} {Y : DerivedModuleCategory A E}
    (r : (kernelDerivedTensor A D E K).obj X ⟶ Y) :
    (kernelDerivedTensor A D E K).map (kernelBrownSuccessor A D E K r).map ≫
      (kernelBrownSuccessor A D E K r).target = r :=
  (kernelBrownSuccessor A D E K r).fac

/-- 実際のkernelの後続操作は、標的射で零になる生成元からの任意の射を消す。 -/
lemma kernelBrownSuccessor_kills {X : DerivedModuleCategory A D} {Y : DerivedModuleCategory A E}
    (r : (kernelDerivedTensor A D E K).obj X ⟶ Y) (p : D × ℤ)
    (f : moduleCompactGenerators A D p ⟶ X)
    (hf : (kernelDerivedTensor A D E K).map f ≫ r = 0) :
    f ≫ (kernelBrownSuccessor A D E K r).map = 0 :=
  (kernelBrownSuccessor A D E K r).kills p f hf

end SerrePositivity.DifferentialGraded.Morita
end

end AdjunctionKernelSuccessor

/-! ## AdjunctionKernelSequence（旧 SerrePositivity/DifferentialGraded/Morita/AdjunctionKernelSequence.lean） -/

/-! # 任意kernelの右随伴を構成する可算近似列

## 概要
生成元被覆から始めて、生成元の全関係を各後続段階で消す可算列を構成する。

## 方針
実際のkernel作用に対する初期射と後続操作を反復し、標的射の互換性を自然なcoconeへまとめる。

## 規約と注意
kernelの列の射影性・局所Hom K-flat性を仮定しない。telescopeでの表現可能性は後続で証明する。

## 使われ方
U16aの一般右随伴の表現対象を、可算telescopeとcompact生成から構成する際の入力。
-/

@[expose] public section AdjunctionKernelSequence
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)
  (Y : DerivedModuleCategory A E)

/-- kernel作用の像からYへの射を持つ一つの近似対象。 -/
structure KernelBrownApproximation where
  obj : DerivedModuleCategory A D
  target : (kernelDerivedTensor A D E K).obj obj ⟶ Y

/-- 近似の生成元の関係を全て消す後続対象。 -/
def kernelBrownApproximationNext (S : KernelBrownApproximation A D E K Y) :
    KernelBrownApproximation A D E K Y :=
  let T := kernelBrownSuccessor A D E K S.target
  ⟨T.obj, T.target⟩

/-- 生成元被覆から始まり、後続操作を反復する可算近似。 -/
def kernelBrownApproximation : ℕ → KernelBrownApproximation A D E K Y
  | 0 => ⟨brownSeed A D E (kernelDerivedTensor A D E K) Y, kernelBrownSeedMap A D E K Y⟩
  | n + 1 => kernelBrownApproximationNext A D E K Y (kernelBrownApproximation n)

/-- 隣り合う近似を結ぶ実際の後続射。 -/
def kernelBrownTransition (n : ℕ) :
    (kernelBrownApproximation A D E K Y n).obj ⟶
      (kernelBrownApproximation A D E K Y (n + 1)).obj :=
  (kernelBrownSuccessor A D E K (kernelBrownApproximation A D E K Y n).target).map

/-- 後続射はYへの標的射を保つ。 -/
lemma kernelBrownTransition_fac (n : ℕ) :
    (kernelDerivedTensor A D E K).map (kernelBrownTransition A D E K Y n) ≫
        (kernelBrownApproximation A D E K Y (n + 1)).target =
      (kernelBrownApproximation A D E K Y n).target :=
  kernelBrownSuccessor_fac A D E K (kernelBrownApproximation A D E K Y n).target

/-- 各段階の生成元からのkernelは、直後の段階で零になる。 -/
lemma kernelBrownTransition_kills (n : ℕ) (p : D × ℤ)
    (f : moduleCompactGenerators A D p ⟶ (kernelBrownApproximation A D E K Y n).obj)
    (hf : (kernelDerivedTensor A D E K).map f ≫
      (kernelBrownApproximation A D E K Y n).target = 0) :
    f ≫ kernelBrownTransition A D E K Y n = 0 :=
  kernelBrownSuccessor_kills A D E K (kernelBrownApproximation A D E K Y n).target p f hf

/-- 生成元のkernel像からYへの全射は、どの近似段階でも表せる。 -/
lemma kernelBrownApproximation_generator_surjective (n : ℕ) (p : D × ℤ)
    (f : (kernelDerivedTensor A D E K).obj (moduleCompactGenerators A D p) ⟶ Y) :
    ∃ g : moduleCompactGenerators A D p ⟶ (kernelBrownApproximation A D E K Y n).obj,
      (kernelDerivedTensor A D E K).map g ≫
        (kernelBrownApproximation A D E K Y n).target = f := by
  induction n with
  | zero => exact kernelBrownSeedMap_generator_surjective A D E K Y p f
  | succ n ih =>
      obtain ⟨g, hg⟩ := ih
      refine ⟨g ≫ kernelBrownTransition A D E K Y n, ?_⟩
      rw [Functor.map_comp, Category.assoc, kernelBrownTransition_fac, hg]

/-- 可算近似と後続射をℕ上の実際の図式へまとめる。 -/
def kernelBrownDiagram : ℕ ⥤ DerivedModuleCategory A D :=
  Functor.ofSequence (kernelBrownTransition A D E K Y)

/-- 可算近似のkernel作用の像からYへの互換なcocone。 -/
def kernelBrownTargetCocone :
    Cocone (kernelBrownDiagram A D E K Y ⋙ kernelDerivedTensor A D E K) where
  pt := Y
  ι := NatTrans.ofSequence (fun n => (kernelBrownApproximation A D E K Y n).target) (by
    intro n
    simp only [kernelBrownDiagram, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ,
      Functor.const_obj_map]
    erw [Category.comp_id]
    exact kernelBrownTransition_fac A D E K Y n)

/-- 可算図式の標的coconeの成分は各段階の標的射そのもの。 -/
lemma kernelBrownTargetCocone_ι (n : ℕ) :
    (kernelBrownTargetCocone A D E K Y).ι.app n =
      (kernelBrownApproximation A D E K Y n).target := rfl

end SerrePositivity.DifferentialGraded.Morita
end

end AdjunctionKernelSequence

/-! ## AdjunctionKernelTelescope（旧 SerrePositivity/DifferentialGraded/Morita/AdjunctionKernelTelescope.lean） -/

/-! # 一般kernel右随伴の可算telescope

## 概要
生成元の関係を順次消す近似列のtelescopeと、そのkernel像から標的への射を構成する。

## 方針
余積保存で各段階の標的射を束ね、三角性とHom完全性でtelescopeへ延長する。

## 規約と注意
局所Hom K-flat性やkernel列の射影性は要求しない。全入力での表現可能性は後続の課題。

## 使われ方
U16aの一般右随伴の表現対象と生成元上のHom同値を構成する。
-/

@[expose] public section AdjunctionKernelTelescope
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Preadditive Pretriangulated
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)
  (Y : DerivedModuleCategory A E)

/-- 可算近似の対象族。 -/
abbrev kernelBrownObjects (n : ℕ) := (kernelBrownApproximation A D E K Y n).obj

/-- 近似の可算余積からのkernel像に定まる標的射。 -/
def kernelBrownSumTarget :
    (kernelDerivedTensor A D E K).obj
      (∐ moduleTelescopeFamily A D (kernelBrownObjects A D E K Y)) ⟶ Y := by
  let := kernelDerivedTensorPreservesCoproducts A D E (J := ULift.{u} ℕ) K
  exact (PreservesCoproduct.iso (kernelDerivedTensor A D E K)
    (moduleTelescopeFamily A D (kernelBrownObjects A D E K Y))).hom ≫
      Sigma.desc (fun n => (kernelBrownApproximation A D E K Y n.down).target)

/-- 可算余積の各挿入射での標的射の計算。 -/
lemma kernelBrownSumTarget_ι (n : ℕ) :
    (kernelDerivedTensor A D E K).map
        (Sigma.ι (moduleTelescopeFamily A D (kernelBrownObjects A D E K Y)) ⟨n⟩) ≫
      kernelBrownSumTarget A D E K Y = (kernelBrownApproximation A D E K Y n).target := by
  let := kernelDerivedTensorPreservesCoproducts A D E (J := ULift.{u} ℕ) K
  dsimp only [kernelBrownSumTarget]
  rw [← ι_comp_sigmaComparison, ← PreservesCoproduct.inv_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Sigma.ι_comp_desc]

/-- 三角性から得る実際のkernel作用の加法性。 -/
lemma kernelBrownActionAdditive : (kernelDerivedTensor A D E K).Additive := by
  let := mainKernelActionCommShift A D E K
  let := mainKernelActionIsTriangulated A D E K
  infer_instance

/-- 互換な標的射は1-shiftのkernel像を消す。 -/
lemma kernelBrownSumTarget_relation :
    (kernelDerivedTensor A D E K).map
      (moduleTelescopeMap A D (kernelBrownObjects A D E K Y)
        (kernelBrownTransition A D E K Y)) ≫ kernelBrownSumTarget A D E K Y = 0 := by
  let L := kernelDerivedTensor A D E K
  let : L.Additive := kernelBrownActionAdditive A D E K
  let F := moduleTelescopeFamily A D (kernelBrownObjects A D E K Y)
  let := kernelDerivedTensorPreservesCoproducts A D E (J := ULift.{u} ℕ) K
  apply (isColimitOfHasCoproductOfPreservesColimit L F).hom_ext
  rintro ⟨⟨n⟩⟩
  change L.map (Sigma.ι F ⟨n⟩) ≫ _ = _
  rw [← L.map_comp_assoc]
  have h : Sigma.ι F ⟨n⟩ ≫ moduleTelescopeMap A D
      (kernelBrownObjects A D E K Y) (kernelBrownTransition A D E K Y) =
      Sigma.ι F ⟨n⟩ - kernelBrownTransition A D E K Y n ≫ Sigma.ι F ⟨n+1⟩ := by
    simp only [moduleTelescopeMap, moduleTelescopeShift, comp_sub, Sigma.ι_comp_desc]
    erw [Category.comp_id]
  rw [h, L.map_sub, sub_comp, L.map_comp, Category.assoc]
  change _ = L.map (Sigma.ι F ⟨n⟩) ≫ 0
  erw [kernelBrownSumTarget_ι A D E K Y n,
    kernelBrownSumTarget_ι A D E K Y (n+1), kernelBrownTransition_fac A D E K Y n]
  exact (sub_self _).trans (comp_zero).symm

/-- 近似列のtelescopeとその像からYへの延長射。 -/
structure KernelBrownTelescope where
  obj : DerivedModuleCategory A D
  inclusion : (∐ moduleTelescopeFamily A D (kernelBrownObjects A D E K Y)) ⟶ obj
  boundary : obj ⟶ (∐ moduleTelescopeFamily A D (kernelBrownObjects A D E K Y))⟦(1 : ℤ)⟧
  distinguished : Triangle.mk
    (moduleTelescopeMap A D (kernelBrownObjects A D E K Y) (kernelBrownTransition A D E K Y))
    inclusion boundary ∈ distTriang (DerivedModuleCategory A D)
  target : (kernelDerivedTensor A D E K).obj obj ⟶ Y
  fac : (kernelDerivedTensor A D E K).map inclusion ≫ target = kernelBrownSumTarget A D E K Y

/-- 三角性と余積保存から、実際のtelescopeと延長射が存在する。 -/
lemma kernelBrownTelescope_nonempty : Nonempty (KernelBrownTelescope A D E K Y) := by
  let L := kernelDerivedTensor A D E K
  let := mainKernelActionCommShift A D E K
  let := mainKernelActionIsTriangulated A D E K
  obtain ⟨Z, c, b, hT⟩ := distinguished_cocone_triangle
    (moduleTelescopeMap A D (kernelBrownObjects A D E K Y) (kernelBrownTransition A D E K Y))
  let T := Triangle.mk
    (moduleTelescopeMap A D (kernelBrownObjects A D E K Y) (kernelBrownTransition A D E K Y)) c b
  obtain ⟨r, hr⟩ := (L.mapTriangle.obj T).yoneda_exact₂ (L.map_distinguished T hT)
    (kernelBrownSumTarget A D E K Y) (kernelBrownSumTarget_relation A D E K Y)
  exact ⟨⟨Z, c, b, hT, r, hr.symm⟩⟩

/-- 構成したtelescopeの一つを選ぶ。 -/
def kernelBrownTelescope : KernelBrownTelescope A D E K Y :=
  Classical.choice (kernelBrownTelescope_nonempty A D E K Y)

variable (S : KernelBrownTelescope A D E K Y)

/-- 各近似段階からtelescopeへの標準射。 -/
def kernelBrownStageMap (n : ℕ) : kernelBrownObjects A D E K Y n ⟶ S.obj :=
  Sigma.ι (moduleTelescopeFamily A D (kernelBrownObjects A D E K Y)) ⟨n⟩ ≫ S.inclusion

/-- telescopeの標準射は各段階の標的射を保つ。 -/
lemma kernelBrownStageMap_fac (n : ℕ) :
    (kernelDerivedTensor A D E K).map (kernelBrownStageMap A D E K Y S n) ≫ S.target =
      (kernelBrownApproximation A D E K Y n).target := by
  rw [kernelBrownStageMap, Functor.map_comp, Category.assoc, S.fac,
    kernelBrownSumTarget_ι]

/-- telescopeの標準射は後続射と互換。 -/
lemma kernelBrownStageMap_succ (n : ℕ) :
    kernelBrownTransition A D E K Y n ≫ kernelBrownStageMap A D E K Y S (n+1) =
      kernelBrownStageMap A D E K Y S n := by
  have h := congrArg (fun k =>
    Sigma.ι (moduleTelescopeFamily A D (kernelBrownObjects A D E K Y)) ⟨n⟩ ≫ k)
    (comp_distTriang_mor_zero₁₂ _ S.distinguished)
  change _ ≫ (moduleTelescopeMap A D (kernelBrownObjects A D E K Y)
    (kernelBrownTransition A D E K Y) ≫ S.inclusion) = _ at h
  have he : kernelBrownStageMap A D E K Y S n =
      kernelBrownTransition A D E K Y n ≫ kernelBrownStageMap A D E K Y S (n+1) := by
    simpa only [moduleTelescopeMap, moduleTelescopeShift, comp_sub, sub_comp,
      Category.comp_id, Category.assoc, Category.id_comp, Sigma.ι_comp_desc_assoc,
      comp_zero, sub_eq_zero, kernelBrownStageMap] using h
  exact he.symm

end SerrePositivity.DifferentialGraded.Morita
end

end AdjunctionKernelTelescope

/-! ## AdjunctionKernelGeneratorHom（旧 SerrePositivity/DifferentialGraded/Morita/AdjunctionKernelGeneratorHom.lean） -/

/-! # 一般kernel右随伴の生成元上のHom比較

## 概要
構成したtelescopeからの標的射が、全てのshiftした代表加群でHom全単射を与える。

## 方針
全射性は初期被覆、単射性はcompact性による有限段階因子分解と直後の関係消去から示す。

## 規約と注意
任意可換環と独立対象宇宙で成立し、局所Hom K-flat性・kernel列の射影性を仮定しない。

## 使われ方
U16aの全入力でのHom表現可能性を局所化帰納で示す際の生成元の基底。
-/

@[expose] public section AdjunctionKernelGeneratorHom
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)
  (Y : DerivedModuleCategory A E) (S : KernelBrownTelescope A D E K Y)

/-- 生成元の像からYへの任意射は、telescopeの像を経由する。 -/
lemma kernelBrownTelescope_generator_surjective (p : D × ℤ)
    (f : (kernelDerivedTensor A D E K).obj (moduleCompactGenerators A D p) ⟶ Y) :
    ∃ g : moduleCompactGenerators A D p ⟶ S.obj,
      (kernelDerivedTensor A D E K).map g ≫ S.target = f := by
  obtain ⟨g, hg⟩ := kernelBrownApproximation_generator_surjective A D E K Y 0 p f
  refine ⟨g ≫ kernelBrownStageMap A D E K Y S 0, ?_⟩
  rw [Functor.map_comp, Category.assoc, kernelBrownStageMap_fac, hg]

/-- 生成元からtelescopeへの射が標的で零なら、それ自体が零。 -/
lemma kernelBrownTelescope_generator_kernel_zero (p : D × ℤ)
    (f : moduleCompactGenerators A D p ⟶ S.obj)
    (hf : (kernelDerivedTensor A D E K).map f ≫ S.target = 0) : f = 0 := by
  obtain ⟨n, g, hg⟩ := moduleCompact_telescope_factor A D
    (kernelBrownObjects A D E K Y) (kernelBrownTransition A D E K Y)
    (moduleCompactGenerators_compact A D p) S.inclusion S.boundary S.distinguished f
  change f = g ≫ kernelBrownStageMap A D E K Y S n at hg
  have hz : (kernelDerivedTensor A D E K).map g ≫
      (kernelBrownApproximation A D E K Y n).target = 0 := by
    rw [hg, Functor.map_comp, Category.assoc, kernelBrownStageMap_fac] at hf
    exact hf
  rw [hg, ← kernelBrownStageMap_succ A D E K Y S n, ← Category.assoc,
    kernelBrownTransition_kills A D E K Y n p g hz, zero_comp]

/-- telescopeの標的射は全てのcompact生成元でHomの全単射を与える。 -/
lemma kernelBrownTelescope_generator_bijective (p : D × ℤ) :
    Function.Bijective (fun f : moduleCompactGenerators A D p ⟶ S.obj =>
      (kernelDerivedTensor A D E K).map f ≫ S.target) := by
  let L := kernelDerivedTensor A D E K
  let : L.Additive := kernelBrownActionAdditive A D E K
  constructor
  · intro f g h
    change L.map f ≫ S.target = L.map g ≫ S.target at h
    apply sub_eq_zero.mp
    apply kernelBrownTelescope_generator_kernel_zero A D E K Y S p (f-g)
    change L.map (f-g) ≫ S.target = 0
    rw [L.map_sub, sub_comp, h, sub_self]
  · exact kernelBrownTelescope_generator_surjective A D E K Y S p

end SerrePositivity.DifferentialGraded.Morita
end

end AdjunctionKernelGeneratorHom

/-! ## AdjunctionHomTriangles（旧 SerrePositivity/DifferentialGraded/Morita/AdjunctionHomTriangles.lean） -/

/-! # 右随伴のHom比較を三角形に沿って拡張する

## 概要
指定射L(R)→YによるHom比較の全単射性を、三角形の両端から中央へ運ぶ。

## 方針
二つのYoneda完全列を追い、全射性には逆回転、単射性にはshiftした第一頂点を用いる。

## 規約と注意
随伴の存在は仮定しない。指定した実際の三角関手と標的射だけを使う。

## 使われ方
U16aのtelescopeの生成元上のHom全単射を全入力へ拡張する局所化帰納。
-/

@[expose] public section AdjunctionHomTriangles
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Preadditive Pretriangulated
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (L : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  [L.CommShift ℤ] [L.IsTriangulated]
  {R : DerivedModuleCategory A D} {Y : DerivedModuleCategory A E} (r : L.obj R ⟶ Y)

/-- 指定射L(R)→Yから定まる入力XでのHom比較。 -/
abbrev brownHomComparison (X : DerivedModuleCategory A D) (f : X ⟶ R) := L.map f ≫ r

/-- Hom比較の単射性から、そのkernelは零。 -/
lemma brownHomComparison_kernel_zero {X : DerivedModuleCategory A D}
    (hX : Function.Injective (brownHomComparison A D E L r X))
    (f : X ⟶ R) (hf : brownHomComparison A D E L r X f = 0) : f = 0 := by
  apply hX
  simpa only [brownHomComparison, L.map_zero, zero_comp] using hf

/-- 両端と必要なshiftでのHom全単射から、三角形中央のHom全単射を得る。 -/
lemma brownHomComparison_triangle (T : Triangle (DerivedModuleCategory A D))
    (hT : T ∈ distTriang (DerivedModuleCategory A D))
    (h1 : Function.Bijective (brownHomComparison A D E L r T.obj₁))
    (h3 : Function.Bijective (brownHomComparison A D E L r T.obj₃))
    (h1s : Function.Surjective (brownHomComparison A D E L r (T.obj₁⟦(1 : ℤ)⟧)))
    (h3s : Function.Injective (brownHomComparison A D E L r T.invRotate.obj₁)) :
    Function.Bijective (brownHomComparison A D E L r T.obj₂) := by
  have hk (f : T.obj₂ ⟶ R) (hf : L.map f ≫ r = 0) : f = 0 := by
    have haf : T.mor₁ ≫ f = 0 := by
      apply brownHomComparison_kernel_zero A D E L r h1.1
      simp only [brownHomComparison, L.map_comp, Category.assoc, hf, comp_zero]
    obtain ⟨g, hg⟩ := T.yoneda_exact₂ hT f haf
    have hbg : L.map T.mor₂ ≫ (L.map g ≫ r) = 0 := by
      rw [← Category.assoc, ← L.map_comp, ← hg, hf]
    obtain ⟨k, hk⟩ := (L.mapTriangle.obj T).yoneda_exact₃ (L.map_distinguished T hT)
      (L.map g ≫ r) hbg
    obtain ⟨a, ha⟩ := h1s ((L.commShiftIso (1 : ℤ)).hom.app T.obj₁ ≫ k)
    change L.map a ≫ r = (L.commShiftIso (1 : ℤ)).hom.app T.obj₁ ≫ k at ha
    have hga : g = T.mor₃ ≫ a := by
      apply h3.1
      change L.map g ≫ r = L.map (T.mor₃ ≫ a) ≫ r
      rw [L.map_comp, Category.assoc, ha]
      change L.map g ≫ r = (L.map T.mor₃ ≫
        (L.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫ k at hk
      simpa only [Category.assoc] using hk
    rw [hg, hga, ← Category.assoc, comp_distTriang_mor_zero₂₃ T hT, zero_comp]
  constructor
  · intro f g h
    apply sub_eq_zero.mp
    apply hk (f-g)
    change L.map f ≫ r = L.map g ≫ r at h
    rw [L.map_sub, sub_comp, h, sub_self]
  · intro f
    obtain ⟨a, ha⟩ := h1.2 (L.map T.mor₁ ≫ f)
    change L.map a ≫ r = L.map T.mor₁ ≫ f at ha
    have hza : T.invRotate.mor₁ ≫ a = 0 := by
      apply brownHomComparison_kernel_zero A D E L r h3s
      change L.map (T.invRotate.mor₁ ≫ a) ≫ r = 0
      have hz := comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang T hT)
      change T.invRotate.mor₁ ≫ T.mor₁ = 0 at hz
      erw [L.map_comp, Category.assoc, ha, ← Category.assoc, ← L.map_comp, hz,
        L.map_zero, zero_comp]
    obtain ⟨b, hb⟩ := T.invRotate.yoneda_exact₂ (inv_rot_of_distTriang T hT) a hza
    change T.obj₂ ⟶ R at b
    change a = T.mor₁ ≫ b at hb
    have hdiff : L.map T.mor₁ ≫ (f - L.map b ≫ r) = 0 := by
      rw [comp_sub, ← Category.assoc, ← L.map_comp, ← hb, ← ha, sub_self]
    obtain ⟨c, hc⟩ := (L.mapTriangle.obj T).yoneda_exact₂ (L.map_distinguished T hT)
      (f - L.map b ≫ r) hdiff
    obtain ⟨d, hd⟩ := h3.2 c
    change L.map d ≫ r = c at hd
    refine ⟨b + T.mor₂ ≫ d, ?_⟩
    change L.map (b + T.mor₂ ≫ d) ≫ r = f
    rw [L.map_add, add_comp, L.map_comp, Category.assoc, hd]
    change f - L.map b ≫ r = L.map T.mor₂ ≫ c at hc
    rw [← hc]
    exact add_sub_cancel _ _

end SerrePositivity.DifferentialGraded.Morita
end

end AdjunctionHomTriangles

/-! ## AdjunctionHomClosure（旧 SerrePositivity/DifferentialGraded/Morita/AdjunctionHomClosure.lean） -/

/-! # 右随伴のHom比較の同型・retract・余積閉性

## 概要
指定射L(R)→YによるHom全単射が成立する入力を、同型・retract・保存される余積で閉じる。

## 方針
retractの挿入射と射影射、余積の普遍性により比較の単射性と全射性を直接運ぶ。

## 規約と注意
随伴や比較の全入力での可逆性は仮定しない。余積保存を明示する。

## 使われ方
U16aの表現可能性の局所化帰納で用いる閉性補題。
-/

@[expose] public section AdjunctionHomClosure
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits ZeroObject Preadditive Pretriangulated
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (L : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  [L.CommShift ℤ] [L.IsTriangulated]
  {R : DerivedModuleCategory A D} {Y : DerivedModuleCategory A E} (r : L.obj R ⟶ Y)

omit [L.CommShift ℤ] [L.IsTriangulated] in
/-- Hom全単射は入力のretractへ制限できる。 -/
lemma brownHomComparison_retract {X Z : DerivedModuleCategory A D} (s : Retract X Z)
    (hZ : Function.Bijective (brownHomComparison A D E L r Z)) :
    Function.Bijective (brownHomComparison A D E L r X) := by
  constructor
  · intro f g h
    change L.map f ≫ r = L.map g ≫ r at h
    have he : s.r ≫ f = s.r ≫ g := by
      apply hZ.1
      change L.map (s.r ≫ f) ≫ r = L.map (s.r ≫ g) ≫ r
      rw [L.map_comp, L.map_comp, Category.assoc, Category.assoc, h]
    have he' := congrArg (fun k => s.i ≫ k) he
    simpa only [← Category.assoc, s.retract, Category.id_comp] using he'
  · intro f
    obtain ⟨g, hg⟩ := hZ.2 (L.map s.r ≫ f)
    change L.map g ≫ r = L.map s.r ≫ f at hg
    refine ⟨s.i ≫ g, ?_⟩
    change L.map (s.i ≫ g) ≫ r = f
    rw [L.map_comp, Category.assoc, hg, ← Category.assoc, ← L.map_comp,
      s.retract, L.map_id, Category.id_comp]

omit [L.CommShift ℤ] [L.IsTriangulated] in
/-- Hom全単射は入力の同型に沿って運べる。 -/
lemma brownHomComparison_iso {X Z : DerivedModuleCategory A D} (e : X ≅ Z)
    (hZ : Function.Bijective (brownHomComparison A D E L r Z)) :
    Function.Bijective (brownHomComparison A D E L r X) :=
  brownHomComparison_retract A D E L r (Retract.ofIso e) hZ

/-- 零対象を入力とするHom比較は全単射。 -/
lemma brownHomComparison_isZero {X : DerivedModuleCategory A D} (hX : IsZero X) :
    Function.Bijective (brownHomComparison A D E L r X) := by
  constructor
  · intro f g _
    exact hX.eq_of_src f g
  · intro f
    exact ⟨0, (L.map_isZero hX).eq_of_src _ _⟩

omit [L.CommShift ℤ] [L.IsTriangulated] in
/-- 保存される余積のHom比較は、各成分のHom全単射から全単射。 -/
lemma brownHomComparison_coproduct {J : Type z} [Small.{u} J]
    (F : J → DerivedModuleCategory A D)
    [PreservesColimit (Discrete.functor F) L]
    (hF : ∀ j, Function.Bijective (brownHomComparison A D E L r (F j))) :
    Function.Bijective (brownHomComparison A D E L r (∐ F)) := by
  constructor
  · intro f g h
    change L.map f ≫ r = L.map g ≫ r at h
    apply Sigma.hom_ext
    intro j
    apply (hF j).1
    change L.map (Sigma.ι F j ≫ f) ≫ r = L.map (Sigma.ι F j ≫ g) ≫ r
    rw [L.map_comp, L.map_comp, Category.assoc, Category.assoc, h]
  · intro f
    choose g hg using fun j => (hF j).2 (L.map (Sigma.ι F j) ≫ f)
    refine ⟨Sigma.desc g, ?_⟩
    apply (isColimitOfHasCoproductOfPreservesColimit L F).hom_ext
    rintro ⟨j⟩
    change L.map (Sigma.ι F j) ≫ (L.map (Sigma.desc g) ≫ r) = L.map (Sigma.ι F j) ≫ f
    rw [← L.map_comp_assoc, Sigma.ι_comp_desc]
    exact hg j

/-- 全整数shiftでHom比較が全単射となる入力の性質。 -/
def brownHomProperty : ObjectProperty (DerivedModuleCategory A D) :=
  fun X => ∀ n : ℤ, Function.Bijective (brownHomComparison A D E L r (X⟦n⟧))

omit [L.CommShift ℤ] [L.IsTriangulated] in
/-- Hom比較の性質は整数shiftで閉じる。 -/
lemma brownHomProperty_shift {X : DerivedModuleCategory A D}
    (hX : brownHomProperty A D E L r X) (a : ℤ) : brownHomProperty A D E L r (X⟦a⟧) := by
  intro b
  exact brownHomComparison_iso A D E L r ((shiftFunctorAdd _ a b).app X).symm (hX (a+b))

/-- Hom比較の性質は同型で閉じる。 -/
instance brownHomPropertyIsClosedUnderIsomorphisms :
    (brownHomProperty A D E L r).IsClosedUnderIsomorphisms where
  of_iso e hX n := brownHomComparison_iso A D E L r
    ((shiftFunctor _ n).mapIso e.symm) (hX n)

/-- Hom比較の性質はretractで閉じる。 -/
instance brownHomPropertyIsStableUnderRetracts :
    (brownHomProperty A D E L r).IsStableUnderRetracts where
  of_retract s hZ n := brownHomComparison_retract A D E L r (s.map (shiftFunctor _ n)) (hZ n)

/-- 全shiftのHom比較の全単射性は三角部分圏を定める。 -/
instance brownHomPropertyIsTriangulated : (brownHomProperty A D E L r).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, fun n =>
    brownHomComparison_isZero A D E L r ((shiftFunctor _ n).map_isZero (isZero_zero _))⟩
  toIsStableUnderShift := ⟨fun a => ⟨fun X hX => brownHomProperty_shift A D E L r hX a⟩⟩
  toIsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk' (by
    intro T hT h1 h3 n
    apply brownHomComparison_triangle A D E L r _ (Triangle.shift_distinguished T hT n)
      (h1 n) (h3 n)
    · exact (brownHomProperty_shift A D E L r h1 n 1).2
    · exact (brownHomProperty_shift A D E L r h3 n (-1)).1)

end SerrePositivity.DifferentialGraded.Morita
end

end AdjunctionHomClosure

/-! ## AdjunctionHomGeneration（旧 SerrePositivity/DifferentialGraded/Morita/AdjunctionHomGeneration.lean） -/

/-! # 生成元のHom比較から全入力の表現可能性へ

## 概要
余積を保つ三角関手と指定射のHom比較が、全shift代表生成元で全単射なら全入力でも全単射。

## 方針
全shiftで比較が全単射となる入力の三角・retract・余積閉性を使い、既存の局所化帰納を適用する。

## 規約と注意
表現可能性の存在を仮定しない。u-small余積保存を明示する。

## 使われ方
U16aの任意kernelのtelescopeから実際の導来右随伴を構成する。
-/

@[expose] public section AdjunctionHomGeneration
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Preadditive Pretriangulated
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (L : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  [L.CommShift ℤ] [L.IsTriangulated]
  {R : DerivedModuleCategory A D} {Y : DerivedModuleCategory A E} (r : L.obj R ⟶ Y)
  (hL : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) L)
include hL

omit [L.CommShift ℤ] [L.IsTriangulated] in
/-- 全shiftのHom比較の全単射性はu-small余積で閉じる。 -/
lemma brownHomProperty_coproduct (J : Type u) (F : J → DerivedModuleCategory A D)
    (hF : ∀ j, brownHomProperty A D E L r (F j)) :
    brownHomProperty A D E L r (∐ F) := by
  intro n
  let := hL J
  apply brownHomComparison_iso A D E L r (PreservesCoproduct.iso (shiftFunctor _ n) F)
  exact brownHomComparison_coproduct A D E L r (fun j => (F j)⟦n⟧) (fun j => hF j n)

/-- 全shift代表生成元での比較から、全主導来入力でのHom全単射を得る。 -/
lemma brownHomComparison_all
    (hgen : ∀ p : D × ℤ,
      Function.Bijective (brownHomComparison A D E L r (moduleCompactGenerators A D p)))
    (X : DerivedModuleCategory A D) :
    Function.Bijective (brownHomComparison A D E L r X) := by
  let P := brownHomProperty A D E L r
  have hperf : ∀ Z : DerivedModuleCategory A D, modulePerfect A D Z → P Z := by
    apply (modulePerfect_le_iff_generators A D P).2
    intro d n
    exact hgen (d,n)
  have hX : P X := moduleLocalizing_all A D P
    (brownHomProperty_coproduct A D E L r hL) hperf X
  exact brownHomComparison_iso A D E L r ((shiftFunctorZero _ ℤ).app X).symm (hX 0)

omit hL

variable (K : Kernel A D E) (Y' : DerivedModuleCategory A E)
  (S : KernelBrownTelescope A D E K Y')

/-- 任意kernelの実際のtelescopeは、全入力でHomを表現する。 -/
lemma kernelBrownTelescope_hom_bijective (X : DerivedModuleCategory A D) :
    Function.Bijective (fun f : X ⟶ S.obj => (kernelDerivedTensor A D E K).map f ≫ S.target) := by
  let := mainKernelActionCommShift A D E K
  let := mainKernelActionIsTriangulated A D E K
  exact brownHomComparison_all A D E (kernelDerivedTensor A D E K) S.target
    (fun J => kernelDerivedTensorPreservesCoproducts A D E (J := J) K)
    (kernelBrownTelescope_generator_bijective A D E K Y' S) X

/-- 任意kernelのtelescopeの全入力Hom比較を同値に束ねる。 -/
def kernelBrownTelescopeHomEquiv (X : DerivedModuleCategory A D) :
    (X ⟶ S.obj) ≃ ((kernelDerivedTensor A D E K).obj X ⟶ Y') :=
  Equiv.ofBijective _ (kernelBrownTelescope_hom_bijective A D E K Y' S X)

end SerrePositivity.DifferentialGraded.Morita
end

end AdjunctionHomGeneration

/-! ## AdjunctionDerived（旧 SerrePositivity/DifferentialGraded/Morita/AdjunctionDerived.lean） -/

/-! # 任意kernelの実際の導来右随伴

## 概要
任意の主導来kernel作用に右随伴を構成し、そのunit/counitと三角恒等式を公開する。

## 方針
telescopeによる全入力のHom表現と始域自然性からMathlibの随伴構成を適用する。

## 規約と注意
任意可換環・非有界複体、独立対象宇宙。局所Hom K-flat性・kernel列の射影性は不要。
随伴の存在を仮定せず、引用を追加しない。

## 使われ方
U16aの一般随伴、U16c統合時の逆同値との比較とunit/counit可逆性。
-/

@[expose] public section AdjunctionDerived
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)

/-- 実際のtelescopeによる、右随伴向きの全入力Hom同値。 -/
def kernelDerivedHomEquiv (X : DerivedModuleCategory A D) (Y : DerivedModuleCategory A E) :
    ((kernelDerivedTensor A D E K).obj X ⟶ Y) ≃
      (X ⟶ (kernelBrownTelescope A D E K Y).obj) :=
  (kernelBrownTelescopeHomEquiv A D E K Y (kernelBrownTelescope A D E K Y) X).symm

/-- Hom同値は始域の全導来射に自然。 -/
lemma kernelDerivedHomEquiv_naturality (X' X : DerivedModuleCategory A D)
    (Y : DerivedModuleCategory A E) (f : X' ⟶ X)
    (g : (kernelDerivedTensor A D E K).obj X ⟶ Y) :
    kernelDerivedHomEquiv A D E K X' Y ((kernelDerivedTensor A D E K).map f ≫ g) =
      f ≫ kernelDerivedHomEquiv A D E K X Y g := by
  let S := kernelBrownTelescope A D E K Y
  let e := kernelBrownTelescopeHomEquiv A D E K Y S
  apply (e X').injective
  change e X' ((e X').symm ((kernelDerivedTensor A D E K).map f ≫ g)) =
    e X' (f ≫ (e X).symm g)
  rw [Equiv.apply_symm_apply]
  change _ = (kernelDerivedTensor A D E K).map (f ≫ (e X).symm g) ≫ S.target
  rw [Functor.map_comp, Category.assoc]
  change _ = (kernelDerivedTensor A D E K).map f ≫ e X ((e X).symm g)
  rw [Equiv.apply_symm_apply]

/-- Hom同値の逆写像はtelescopeの標的射による実際の比較。 -/
lemma kernelDerivedHomEquiv_symm_apply (X : DerivedModuleCategory A D)
    (Y : DerivedModuleCategory A E) (f : X ⟶ (kernelBrownTelescope A D E K Y).obj) :
    (kernelDerivedHomEquiv A D E K X Y).symm f =
      (kernelDerivedTensor A D E K).map f ≫ (kernelBrownTelescope A D E K Y).target := rfl

/-- 任意kernelの実際の導来右随伴。 -/
def kernelDerivedHom : DerivedModuleCategory A E ⥤ DerivedModuleCategory A D :=
  Adjunction.rightAdjointOfEquiv (kernelDerivedHomEquiv A D E K)
    (kernelDerivedHomEquiv_naturality A D E K)

/-- 任意kernel作用と実際の導来Homの随伴。 -/
def kernelDerivedAdjunction : kernelDerivedTensor A D E K ⊣ kernelDerivedHom A D E K :=
  Adjunction.adjunctionOfEquivRight (kernelDerivedHomEquiv A D E K)
    (kernelDerivedHomEquiv_naturality A D E K)

/-- 実際の導来随伴の単位。 -/
def kernelDerivedUnit : 𝟭 (DerivedModuleCategory A D) ⟶
    kernelDerivedTensor A D E K ⋙ kernelDerivedHom A D E K :=
  (kernelDerivedAdjunction A D E K).unit

/-- 実際の導来随伴の余単位。 -/
def kernelDerivedCounit : kernelDerivedHom A D E K ⋙ kernelDerivedTensor A D E K ⟶
    𝟭 (DerivedModuleCategory A E) :=
  (kernelDerivedAdjunction A D E K).counit

/-- 右随伴の値は構成済みtelescopeそのもの。 -/
lemma kernelDerivedHom_obj (Y : DerivedModuleCategory A E) :
    (kernelDerivedHom A D E K).obj Y = (kernelBrownTelescope A D E K Y).obj := rfl

/-- 実際の余単位はtelescopeを構成した標的射と一致する。 -/
lemma kernelDerivedCounit_model (Y : DerivedModuleCategory A E) :
    (kernelDerivedCounit A D E K).app Y = (kernelBrownTelescope A D E K Y).target := by
  change (kernelDerivedTensor A D E K).map (𝟙 _) ≫ _ = _
  rw [CategoryTheory.Functor.map_id]
  erw [Category.id_comp]
  rfl

/-- 実際の導来単位・余単位の左三角恒等式。 -/
lemma kernelDerived_left_triangle (X : DerivedModuleCategory A D) :
    (kernelDerivedTensor A D E K).map ((kernelDerivedUnit A D E K).app X) ≫
      (kernelDerivedCounit A D E K).app ((kernelDerivedTensor A D E K).obj X) = 𝟙 _ :=
  (kernelDerivedAdjunction A D E K).left_triangle_components X

/-- 実際の導来単位・余単位の右三角恒等式。 -/
lemma kernelDerived_right_triangle (Y : DerivedModuleCategory A E) :
    (kernelDerivedUnit A D E K).app ((kernelDerivedHom A D E K).obj Y) ≫
      (kernelDerivedHom A D E K).map ((kernelDerivedCounit A D E K).app Y) = 𝟙 _ :=
  (kernelDerivedAdjunction A D E K).right_triangle_components Y

end SerrePositivity.DifferentialGraded.Morita
end

end AdjunctionDerived

/-! ## CriterionDerivedFullyFaithful（旧 SerrePositivity/DifferentialGraded/Morita/CriterionDerivedFullyFaithful.lean） -/

/-! # Perf上のHom比較を全主導来対象へ広げる二段階の局所化帰納

終域変数はcompactな始域と像のcompact性で、始域変数は余積の普遍性で扱う。
最後の始域帰納には既存の指定射のHom比較補題を恒等射に適用するだけで、
一般右随伴やその存在・unit/counitは使わない。
-/

@[expose] public section CriterionDerivedFullyFaithful
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  [T.CommShift ℤ] [T.IsTriangulated]
  {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
  (hG : CriterionDerivedCompactGeneration A D G)
  (hcop : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) T)
  (hperf : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
  (hhom : ∀ (X Y : DerivedModuleCategory A D), modulePerfect A D X →
    modulePerfect A D Y → Function.Bijective (fun f : X ⟶ Y => T.map f))
include hG hcop hperf hhom

/-- 始域がperfectなら、終域のcompact生成から任意終域でHom比較が全単射となる。 -/
lemma criterionDerivedHom_fromPerfect_all (X : DerivedModuleCategory A D)
    (hX : modulePerfect A D X) (Y : DerivedModuleCategory A D) :
    Function.Bijective (fun f : X ⟶ Y => T.map f) := by
  let P := criterionDerivedHomTargetLocus A D E T X
  have hgen : ∀ i, P (G i) := by
    intro i n
    exact hhom X _ hX (modulePerfect_shift A D (moduleCompact_perfect A D (hG.compact i)) n)
  have hY : P Y := hG.localizing P
    (criterionDerivedHomTargetLocus_coproduct A D E T X hcop
      (modulePerfect_compact A D hX) (modulePerfect_compact A E (hperf X hX))) hgen Y
  exact criterionDerivedHom_target_iso A D E T X
    ((shiftFunctorZero _ ℤ).app Y).symm (hY 0)

/-- 二つ目の帰納を始域に適用し、全主導来対象間のHom比較を全単射にする。 -/
lemma criterionDerivedHom_all (X Y : DerivedModuleCategory A D) :
    Function.Bijective (fun f : X ⟶ Y => T.map f) := by
  have h := brownHomComparison_all A D E T (𝟙 (T.obj Y)) hcop
    (fun p => by
      change Function.Bijective
        (fun f : moduleCompactGenerators A D p ⟶ Y => T.map f ≫ 𝟙 (T.obj Y))
      simpa only [Category.comp_id] using
        criterionDerivedHom_fromPerfect_all A D E T G hG hcop hperf hhom
          (moduleCompactGenerators A D p)
          (moduleCompact_perfect A D (moduleCompactGenerators_compact A D p)) Y) X
  change Function.Bijective (fun f : X ⟶ Y => T.map f ≫ 𝟙 (T.obj Y)) at h
  simpa only [Category.comp_id] using h

/-- Perf上の充満忠実な比較から、実際の全主導来関手の充満忠実性を得る。 -/
def criterionDerivedFullyFaithful : T.FullyFaithful := by
  let : T.Full := ⟨fun {X Y} => (criterionDerivedHom_all A D E T G hG hcop hperf hhom X Y).2⟩
  let : T.Faithful := ⟨fun {X Y} => (criterionDerivedHom_all A D E T G hG hcop hperf hhom X Y).1⟩
  exact Functor.FullyFaithful.ofFullyFaithful T

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionDerivedFullyFaithful

/-! ## CriterionDerivedEquivalence（旧 SerrePositivity/DifferentialGraded/Morita/CriterionDerivedEquivalence.lean） -/

/-! # Perf上の同値から全主導来圏へのMorita拡張

Perf判定の結論は明示した入力とする。両側のcompact生成を保持し、
右随伴・その一致・unit/counitとの比較は構成しない。
-/

@[expose] public section CriterionDerivedEquivalence
universe u v w z z'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)

/-- 実際のPerf制限の同値から、元の関手のPerf対象間のHom比較を取り出す。 -/
lemma criterionDerivedHom_of_perfectEquivalence
    (hperf : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    [(perfectFunctorRestriction A D E T hperf).IsEquivalence]
    (X Y : DerivedModuleCategory A D) (hX : modulePerfect A D X) (hY : modulePerfect A D Y) :
    Function.Bijective (fun f : X ⟶ Y => T.map f) := by
  let F := perfectFunctorRestriction A D E T hperf
  let X' : PerfectModuleCategory A D := ⟨X, hX⟩
  let Y' : PerfectModuleCategory A D := ⟨Y, hY⟩
  constructor
  · intro f g h
    change T.map f = T.map g at h
    have he : F.map (ObjectProperty.homMk f : X' ⟶ Y') =
        F.map (ObjectProperty.homMk g : X' ⟶ Y') := (modulePerfect A E).hom_ext h
    exact congrArg (fun k : X' ⟶ Y' => k.hom) (F.map_injective he)
  · intro g
    obtain ⟨f, hf⟩ := F.map_surjective (ObjectProperty.homMk g : F.obj X' ⟶ F.obj Y')
    exact ⟨f.hom, congrArg (fun k : F.obj X' ⟶ F.obj Y' => k.hom) hf⟩

/-- 実際のPerf制限の本質的全射を、主導来圏での本質的像として読む。 -/
lemma criterionDerivedImage_of_perfectEquivalence
    (hperf : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    [(perfectFunctorRestriction A D E T hperf).EssSurj]
    (Y : DerivedModuleCategory A E) (hY : modulePerfect A E Y) : T.essImage Y := by
  let F := perfectFunctorRestriction A D E T hperf
  let Y' : PerfectModuleCategory A E := ⟨Y, hY⟩
  exact ⟨(F.objPreimage Y').obj,
    ⟨(perfectModuleInclusion A E Set.univ).mapIso (F.objObjPreimageIso Y')⟩⟩

variable [T.CommShift ℤ] [T.IsTriangulated]

/-- 明示した両側のcompact生成の下で、Perf同値を全主導来圏の同値性へ拡張する。 -/
lemma criterionDerivedIsEquivalence_of_perfectEquivalence
    (hperf : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    [(perfectFunctorRestriction A D E T hperf).IsEquivalence]
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H)
    (hcop : ∀ K : Type u, PreservesColimitsOfShape (Discrete K) T) : T.IsEquivalence := by
  let hff := criterionDerivedFullyFaithful A D E T G hG hcop hperf
    (criterionDerivedHom_of_perfectEquivalence A D E T hperf)
  let : T.Full := hff.full
  let : T.Faithful := hff.faithful
  let : T.EssSurj := criterionDerivedEssSurj_of_perfectImage A D E T hcop H hH
    (criterionDerivedImage_of_perfectEquivalence A D E T hperf)
  exact {}

/-- 順関手を元の実際の関手のままに保つ、条件付きの全主導来圏同値。 -/
def criterionDerivedEquivalence_of_perfectEquivalence
    (hperf : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    [(perfectFunctorRestriction A D E T hperf).IsEquivalence]
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H)
    (hcop : ∀ K : Type u, PreservesColimitsOfShape (Discrete K) T) :
    DerivedModuleCategory A D ≌ DerivedModuleCategory A E := by
  have := criterionDerivedIsEquivalence_of_perfectEquivalence A D E T hperf G hG H hH hcop
  exact T.asEquivalence

omit [T.CommShift ℤ] [T.IsTriangulated]

/-- 一般kernelのPerf同値から、実際の主導来作用の同値性を得る。
三角性と余積保存は既存の実際の作用のAPIから供給する。 -/
lemma criterionDerivedKernelIsEquivalence (K : Kernel A D E)
    (hK : kernelColumnsPerfect A D E K)
    [(perfectDerivedKernelAction A D E K hK).IsEquivalence]
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    (kernelDerivedTensor A D E K).IsEquivalence := by
  let := criterionPerfKernelCommShift A D E K
  let := criterionPerfKernelIsTriangulated A D E K
  let hperf : ∀ X, modulePerfect A D X →
      modulePerfect A E ((kernelDerivedTensor A D E K).obj X) :=
    fun _ h => perfectDerivedKernelAction_preserves A D E K hK h
  let : (perfectFunctorRestriction A D E (kernelDerivedTensor A D E K) hperf).IsEquivalence := by
    change (perfectDerivedKernelAction A D E K hK).IsEquivalence
    infer_instance
  exact criterionDerivedIsEquivalence_of_perfectEquivalence A D E
    (kernelDerivedTensor A D E K) hperf G hG H hH
    (fun J => criterionDerivedKernelPreservesCoproducts A D E K J)

/-- compact生成を明示した、一般kernelによる全主導来圏のMorita同値。 -/
def criterionDerivedKernelEquivalence (K : Kernel A D E)
    (hK : kernelColumnsPerfect A D E K)
    [(perfectDerivedKernelAction A D E K hK).IsEquivalence]
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    DerivedModuleCategory A D ≌ DerivedModuleCategory A E := by
  have := criterionDerivedKernelIsEquivalence A D E K hK G hG H hH
  exact (kernelDerivedTensor A D E K).asEquivalence

lemma criterionDerivedKernelEquivalence_functor (K : Kernel A D E)
    (hK : kernelColumnsPerfect A D E K)
    [(perfectDerivedKernelAction A D E K hK).IsEquivalence]
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    (criterionDerivedKernelEquivalence A D E K hK G hG H hH).functor =
      kernelDerivedTensor A D E K := rfl

/-- CriterionPerf側の実際の同値の証拠を、そのまま全主導来圏同値へ拡張する。 -/
def criterionDerivedKernelEquivalenceOfPerfWitness (K : Kernel A D E)
    (W : CriterionPerfEquivalenceWitness A D E K)
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    DerivedModuleCategory A D ≌ DerivedModuleCategory A E := by
  have := W.actionIsEquivalence A D E K
  exact criterionDerivedKernelEquivalence A D E K (W.columnsPerfect A D E K) G hG H hH

lemma criterionDerivedKernelEquivalenceOfPerfWitness_functor (K : Kernel A D E)
    (W : CriterionPerfEquivalenceWitness A D E K)
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    (criterionDerivedKernelEquivalenceOfPerfWitness A D E K W G hG H hH).functor =
      kernelDerivedTensor A D E K := rfl

/-- 全導来圏同値をPerfへ制限する図式は、元の実際のPerf同値の比較を保つ。 -/
def criterionDerivedKernelEquivalenceOfPerfWitness_inclusion (K : Kernel A D E)
    (W : CriterionPerfEquivalenceWitness A D E K)
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    perfectModuleInclusion A D Set.univ ⋙
        (criterionDerivedKernelEquivalenceOfPerfWitness A D E K W G hG H hH).functor ≅
      W.equivalence.functor ⋙ perfectModuleInclusion A E Set.univ :=
  W.comparison

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionDerivedEquivalence

/-! ## CriterionDerivedConditions（旧 SerrePositivity/DifferentialGraded/Morita/CriterionDerivedConditions.lean） -/

/-! # Perf判定の十分性を明示した入力とする全導来Morita拡張

他担当の三条件そのものを用いる。従来の十分性を入力するAPIを保ち、
完成したPerf判定でその入力を供給する版も公開する。
-/

@[expose] public section CriterionDerivedConditions
universe u v w z z'

noncomputable section
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 三条件から実際のPerf同値の証拠を得る十分性定理の型。
従来の条件付きAPIの入力型を保持する。成立は後の補題で証明する。 -/
def CriterionDerivedPerfSufficiency : Prop :=
  ∀ K : Kernel A D E, CriterionPerfConditions A D E K →
    Nonempty (CriterionPerfEquivalenceWitness A D E K)

/-- Perf十分性定理を入力として、元の三条件とcompact生成から主作用の同値性を得る。 -/
lemma criterionDerivedKernelIsEquivalenceOfConditions
    (hPerf : CriterionDerivedPerfSufficiency A D E)
    (K : Kernel A D E) (hK : CriterionPerfConditions A D E K)
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    (kernelDerivedTensor A D E K).IsEquivalence := by
  obtain ⟨W⟩ := hPerf K hK
  have := W.actionIsEquivalence A D E K
  exact criterionDerivedKernelIsEquivalence A D E K (W.columnsPerfect A D E K) G hG H hH

/-- 三条件を元の型のまま受け取る、明示的に条件付きの全主導来圏Morita同値。 -/
def criterionDerivedKernelEquivalenceOfConditions
    (hPerf : CriterionDerivedPerfSufficiency A D E)
    (K : Kernel A D E) (hK : CriterionPerfConditions A D E K)
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    DerivedModuleCategory A D ≌ DerivedModuleCategory A E := by
  have := criterionDerivedKernelIsEquivalenceOfConditions A D E hPerf K hK G hG H hH
  exact (kernelDerivedTensor A D E K).asEquivalence

lemma criterionDerivedKernelEquivalenceOfConditions_functor
    (hPerf : CriterionDerivedPerfSufficiency A D E)
    (K : Kernel A D E) (hK : CriterionPerfConditions A D E K)
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    (criterionDerivedKernelEquivalenceOfConditions A D E hPerf K hK G hG H hH).functor =
      kernelDerivedTensor A D E K := rfl

/-- 完成した一般kernelのPerf判定は、従来の十分性入力を供給する。 -/
lemma criterionDerivedPerfSufficiency : CriterionDerivedPerfSufficiency A D E :=
  fun K hK => ⟨criterionPerfEquivalenceOfConditions A D E K hK⟩

/-- 三条件と両側のcompact生成から、実際の主導来kernel作用は同値である。 -/
lemma criterionDerivedKernelIsEquivalenceOfMoritaConditions
    (K : Kernel A D E) (hK : CriterionPerfConditions A D E K)
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    (kernelDerivedTensor A D E K).IsEquivalence :=
  criterionDerivedKernelIsEquivalenceOfConditions A D E
    (criterionDerivedPerfSufficiency A D E) K hK G hG H hH

/-- Perf十分性の追加入力を要しない、三条件による全主導来圏Morita同値。 -/
def criterionDerivedKernelEquivalenceOfMoritaConditions
    (K : Kernel A D E) (hK : CriterionPerfConditions A D E K)
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    DerivedModuleCategory A D ≌ DerivedModuleCategory A E :=
  criterionDerivedKernelEquivalenceOfConditions A D E
    (criterionDerivedPerfSufficiency A D E) K hK G hG H hH

/-- 構成した同値の順方向は、既存の主導来tensor作用そのものである。 -/
lemma criterionDerivedKernelEquivalenceOfMoritaConditions_functor
    (K : Kernel A D E) (hK : CriterionPerfConditions A D E K)
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    (criterionDerivedKernelEquivalenceOfMoritaConditions A D E K hK G hG H hH).functor =
      kernelDerivedTensor A D E K := rfl

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionDerivedConditions
