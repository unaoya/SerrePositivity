module

public import SerrePositivity.DifferentialGraded.Morita.Perfect
public import SerrePositivity.DifferentialGraded.Module.EvaluationReflects
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKernel
public import SerrePositivity.DifferentialGraded.Verdier.Derived
public import SerrePositivity.DifferentialGraded.Endomorphism.Derived.Functors
public import SerrePositivity.DifferentialGraded.Perfect.Compact.FiniteGeneration
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Morita.CriterionDerivedCoproducts

## 概要
7 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## AdjunctionKernelColimits（旧 SerrePositivity/DifferentialGraded/Morita/AdjunctionKernelColimits.lean） -/

/-! # 任意kernelの通常作用の余極限保存

## 概要
右E・左D kernelの通常tensor作用がu-small図式の余極限を保存することを証明する。

## 方針
出力評価を既存のbalanced tensor左随伴へ比較し、加群の評価による余極限反映を使う。

## 規約と注意
係数は任意可換環。kernelの射影性・局所Hom K-flat性は要求しない。
添字の対象はSmall.{u}で、射の宇宙は独立。

## 使われ方
U16aの主導来kernel作用の余積保存と一般右随伴の表現対象構成に使う。
-/

@[expose] public section AdjunctionKernelColimits
universe u v w z z'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)
  {J : Type z} [Category.{z'} J] [Small.{u} J]

/-- 評価とbalanced tensorとの比較から、通常kernel作用が余極限coconeを保存する。 -/
def kernelTensorIsColimit {F : J ⥤ ModuleCategory A D} (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((kernelTensor A D E P).onClosed.mapCocone c) := by
  apply moduleIsColimitOfEvaluations A E
  intro e
  let : PreservesColimit F ((kernelTensor A D E P).onClosed ⋙ moduleEvaluation A E e) :=
    preservesColimit_of_natIso F (perfectKernelTensorEvaluationIso A D E P e).symm
  exact isColimitOfPreserves ((kernelTensor A D E P).onClosed ⋙ moduleEvaluation A E e) hc

/-- 任意kernelの通常作用は、対象添字がu-smallな図式の余極限を保存する。 -/
instance kernelTensorPreservesColimitsOfShape :
    PreservesColimitsOfShape J (kernelTensor A D E P).onClosed where
  preservesColimit {F} :=
    preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
      (kernelTensorIsColimit A D E P (colimit.cocone F) (colimit.isColimit F))

end SerrePositivity.DifferentialGraded.Morita
end

end AdjunctionKernelColimits

/-! ## AdjunctionKernelCoproducts（旧 SerrePositivity/DifferentialGraded/Morita/AdjunctionKernelCoproducts.lean） -/

/-! # 任意の主導来kernel作用の余積保存

## 概要
任意kernelの実際の主導来作用がu-small余積を保存することを証明する。

## 方針
射影的な入力族とその余積で増大比較を反転し、既存の主局所化の余積保存へ帰着する。
任意の導来族は指定射影解像度の族へ比較する。

## 規約と注意
kernelの列の射影性・局所Hom K-flat性を仮定しない。射影性は入力の計算モデルだけに使う。
対象宇宙は独立で、余積添字はSmall.{u}。

## 使われ方
U16aの一般右随伴を構成する生成元被覆・関係除去・可算telescopeへ実際の余積保存を供給する。
-/

@[expose] public section AdjunctionKernelCoproducts
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)
  {J : Type z} [Small.{u} J]

/-- 射影入力族の導来余積を作用で写したcofanは、出力側でも余積。 -/
def kernelDerivedTensorProjectiveCofanIsColimit (M : J → ModuleCategory A D)
    (hM : ∀ j, moduleHomotopicallyProjective A D (M j)) :
    IsColimit ((kernelDerivedTensorOnBimodule A D E P).mapCocone
      (moduleProjectiveDerivedCofan A D M)) := by
  let T := kernelDerivedTensorOnBimodule A D E P
  let G := (kernelTensor A D E P).onClosed ⋙ moduleToDerived A E
  let η := kernelDerivedTensorAugmentation A D E P
  let C := G.mapCocone (colimit.cocone (Discrete.functor M))
  let e : Discrete.functor (fun j => (moduleToDerived A D).obj (M j)) ⋙ T ≅
      Discrete.functor M ⋙ G :=
    Discrete.natIso (fun j => by
      have := kernelDerivedTensorAugmentation_isIso_of_relativeKFlat A D E P (M j.as)
        (moduleHomotopicallyProjective_relativeKFlat A D (hM j.as))
      exact asIso (η.app (M j.as)))
  have := kernelDerivedTensorAugmentation_isIso_of_relativeKFlat A D E P (∐ M)
    (moduleHomotopicallyProjective_relativeKFlat A D
      (moduleCoproduct_homotopicallyProjective A D M hM))
  let ep := asIso (η.app (∐ M))
  have hC : IsColimit C := isColimitOfPreserves G (coproductIsCoproduct M)
  have hp := (IsColimit.precomposeHomEquiv e C).symm hC
  refine IsColimit.ofIsoColimit hp (Cocone.ext ep ?_).symm
  rintro ⟨j⟩
  exact η.naturality (Sigma.ι M j)

/-- 通常kernelの導来作用は、射影入力族の主導来像の余積を保存する。 -/
lemma kernelDerivedTensorPreservesProjectiveCoproduct (M : J → ModuleCategory A D)
    (hM : ∀ j, moduleHomotopicallyProjective A D (M j)) :
    PreservesColimit (Discrete.functor (fun j => (moduleToDerived A D).obj (M j)))
      (kernelDerivedTensorOnBimodule A D E P) :=
  preservesColimit_of_preserves_colimit_cocone
    (moduleProjectiveDerivedCofanIsColimit A D M hM)
    (kernelDerivedTensorProjectiveCofanIsColimit A D E P M hM)

/-- 任意の導来入力族を射影解像度の族へ比較して、余積保存を得る。 -/
instance kernelDerivedTensorOnBimodulePreservesCoproduct (F : J → DerivedModuleCategory A D) :
    PreservesColimit (Discrete.functor F) (kernelDerivedTensorOnBimodule A D E P) := by
  let R := fun j => moduleCanonicalProjectiveResolution A D (F j).as.obj
  let M := fun j => (R j).obj
  let := kernelDerivedTensorPreservesProjectiveCoproduct A D E P M (fun j => (R j).projective)
  let e : Discrete.functor (fun j => (moduleToDerived A D).obj (M j)) ≅ Discrete.functor F :=
    Discrete.natIso (fun j => moduleDerivedIso A D (R j.as).π (R j.as).quasiIso)
  exact preservesColimit_of_iso_diagram (kernelDerivedTensorOnBimodule A D E P) e

/-- 任意通常kernelの主導来作用はu-small余積を保存する。 -/
instance kernelDerivedTensorOnBimodulePreservesCoproducts :
    PreservesColimitsOfShape (Discrete J) (kernelDerivedTensorOnBimodule A D E P) :=
  preservesColimitsOfShape_of_discrete _

/-- 主局所化上の任意kernelの作用もu-small余積を保存する。 -/
lemma kernelDerivedTensorPreservesCoproducts (K : Kernel A D E) :
    PreservesColimitsOfShape (Discrete J) (kernelDerivedTensor A D E K) := by
  obtain ⟨⟨Q⟩⟩ := K
  exact preservesColimitsOfShape_of_natIso (kernelDerivedTensorOnBimoduleIso A D E Q).symm

end SerrePositivity.DifferentialGraded.Morita
end

end AdjunctionKernelCoproducts

/-! ## CriterionDerivedCoproducts（旧 SerrePositivity/DifferentialGraded/Morita/CriterionDerivedCoproducts.lean） -/

/-! # 右随伴を使わないMorita拡張の余積保存

既存のtensor計算による余積保存を使う。一般導来右随伴・unit/counitは使わない。
-/

@[expose] public section CriterionDerivedCoproducts
universe u v w z

noncomputable section
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 任意の主導来kernelの実際の作用はu-small余積を保存する。 -/
lemma criterionDerivedKernelPreservesCoproducts (K : Kernel A D E)
    (J : Type z) [Small.{u} J] :
    PreservesColimitsOfShape (Discrete J) (kernelDerivedTensor A D E K) :=
  kernelDerivedTensorPreservesCoproducts A D E K

/-- 余積を保存する関手の本質的像は、離散余積で閉じる。充満忠実性は不要。 -/
lemma criterionDerivedEssImage_coproduct
    (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    {J : Type z} [Small.{u} J] [PreservesColimitsOfShape (Discrete J) T]
    (F : J → DerivedModuleCategory A E) (hF : ∀ j, T.essImage (F j)) :
    T.essImage (∐ F) := by
  classical
  let X : J → DerivedModuleCategory A D := fun j => (hF j).choose
  let e (j : J) : T.obj (X j) ≅ F j := (hF j).choose_spec.some
  exact ⟨∐ X, ⟨PreservesCoproduct.iso T X ≪≫ Sigma.mapIso e⟩⟩

/-- 主導来kernel作用の本質的像の余積閉性。 -/
lemma criterionDerivedKernelEssImage_coproduct (K : Kernel A D E)
    {J : Type z} [Small.{u} J] (F : J → DerivedModuleCategory A E)
    (hF : ∀ j, (kernelDerivedTensor A D E K).essImage (F j)) :
    (kernelDerivedTensor A D E K).essImage (∐ F) := by
  let := criterionDerivedKernelPreservesCoproducts A D E K J
  exact criterionDerivedEssImage_coproduct A D E _ F hF

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionDerivedCoproducts

/-! ## CriterionDerivedGeneration（旧 SerrePositivity/DifferentialGraded/Morita/CriterionDerivedGeneration.lean） -/

/-! # 明示したcompact生成による本質的像の局所化帰納

生成族の各対象のcompact性と、余積閉三角部分圏による生成を別々に保持する。
充満性を得る前に本質的像の三角閉性を仮定することはしない。
-/

@[expose] public section CriterionDerivedGeneration
universe u v w z

noncomputable section
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 各生成元のcompact性と、u-small余積・錐・shiftによる全対象の生成。 -/
structure CriterionDerivedCompactGeneration {I : Type z} [Small.{u} I]
    (G : I → DerivedModuleCategory A D) : Prop where
  compact : ∀ i, moduleCompact A D (G i)
  localizing : ∀ (P : ObjectProperty (DerivedModuleCategory A D))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms],
    (∀ (J : Type u) (F : J → DerivedModuleCategory A D), (∀ j, P (F j)) → P (∐ F)) →
    (∀ i, P (G i)) → ∀ X, P X

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  [T.CommShift ℤ] [T.IsTriangulated] [T.Full]
  (hcop : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) T)

include hcop in
/-- 充満な三角関手の本質的像がcompact生成族を含めば、全対象を含む。
右随伴による像の記述は使わない。 -/
lemma criterionDerivedEssSurj_of_compactGeneration
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A E)
    (hG : CriterionDerivedCompactGeneration A E G)
    (himage : ∀ i, T.essImage (G i)) : T.EssSurj := by
  refine ⟨fun X => hG.localizing T.essImage ?_ himage X⟩
  intro J F hF
  let := hcop J
  exact criterionDerivedEssImage_coproduct A D E T F hF

include hcop in
/-- Perf上の本質的全射と明示したcompact生成を、全対象の本質的全射へ拡張する。
三角性・充満性は入力とし、充満忠実性の局所化帰納とは分ける。 -/
lemma criterionDerivedEssSurj_of_perfectImage
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A E)
    (hG : CriterionDerivedCompactGeneration A E G)
    (hperf : ∀ Y : DerivedModuleCategory A E, modulePerfect A E Y → T.essImage Y) :
    T.EssSurj :=
  criterionDerivedEssSurj_of_compactGeneration A D E T hcop G hG
    (fun i => hperf _ (moduleCompact_perfect A E (hG.compact i)))

/-- 一般kernelの作用についても、同じ右随伴なしの局所化帰納を使う。 -/
lemma criterionDerivedKernelEssSurj_of_perfectImage (K : Kernel A D E)
    [(kernelDerivedTensor A D E K).CommShift ℤ]
    [(kernelDerivedTensor A D E K).IsTriangulated]
    [(kernelDerivedTensor A D E K).Full]
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A E)
    (hG : CriterionDerivedCompactGeneration A E G)
    (hperf : ∀ Y : DerivedModuleCategory A E, modulePerfect A E Y →
      (kernelDerivedTensor A D E K).essImage Y) :
    (kernelDerivedTensor A D E K).EssSurj :=
  criterionDerivedEssSurj_of_perfectImage A D E (kernelDerivedTensor A D E K)
    (fun J => criterionDerivedKernelPreservesCoproducts A D E K J) G hG hperf

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionDerivedGeneration

/-! ## CriterionDerivedHomCoproducts（旧 SerrePositivity/DifferentialGraded/Morita/CriterionDerivedHomCoproducts.lean） -/

/-! # compact始域に対するHom比較の余積閉性

各生成元のcompact性だけを使い、生成族全体の直和をcompactとは仮定しない。
一般の導来右随伴は使わない。
-/

@[expose] public section CriterionDerivedHomCoproducts
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E) [T.Additive]
  {J : Type u} (F : J → DerivedModuleCategory A D) (X : DerivedModuleCategory A D)

/-- compactな始域からのHom比較の単射性は、終域のu-small余積で保たれる。 -/
lemma criterionDerivedHom_coproduct_injective (hX : moduleCompact A D X)
    (hF : ∀ j, Function.Injective (fun f : X ⟶ F j => T.map f)) :
    Function.Injective (fun f : X ⟶ ∐ F => T.map f) := by
  intro f g hfg
  change T.map f = T.map g at hfg
  apply sub_eq_zero.mp
  apply moduleCompact_hom_ext_zero A D hX F (f - g)
  intro j
  apply hF j
  change T.map ((f - g) ≫ moduleDerivedCoproductProjection A D F j) = T.map 0
  rw [CategoryTheory.Functor.map_comp, Functor.map_sub, hfg, sub_self,
    zero_comp, Functor.map_zero]

/-- compactな像と余積保存から、終域の余積へのHom比較の全射性を得る。 -/
lemma criterionDerivedHom_coproduct_surjective
    [PreservesColimit (Discrete.functor F) T]
    (hTX : moduleCompact A E (T.obj X))
    (hF : ∀ j, Function.Surjective (fun f : X ⟶ F j => T.map f)) :
    Function.Surjective (fun f : X ⟶ ∐ F => T.map f) := by
  classical
  intro f
  let e := PreservesCoproduct.iso T F
  obtain ⟨s, g, hg⟩ := hTX J (fun j => T.obj (F j)) (f ≫ e.hom)
  let a (j : J) : X ⟶ F j := (hF j (g j)).choose
  have ha (j : J) : T.map (a j) = g j := (hF j (g j)).choose_spec
  refine ⟨∑ j ∈ s, a j ≫ Sigma.ι F j, ?_⟩
  calc
    _ = ∑ j ∈ s, g j ≫ T.map (Sigma.ι F j) := by
      simp only [Functor.map_sum, CategoryTheory.Functor.map_comp, ha]
    _ = (∑ j ∈ s, g j ≫ Sigma.ι (fun j => T.obj (F j)) j) ≫
        sigmaComparison T F := by
      simp only [sum_comp, Category.assoc, ι_comp_sigmaComparison]
    _ = (f ≫ e.hom) ≫ e.inv := congrArg (fun k => k ≫ e.inv) hg
    _ = f := by rw [Category.assoc, e.hom_inv_id, Category.comp_id]

/-- 各compact生成元について使う、Hom比較の全単射性の余積閉性。 -/
lemma criterionDerivedHom_coproduct_bijective
    [PreservesColimit (Discrete.functor F) T]
    (hX : moduleCompact A D X) (hTX : moduleCompact A E (T.obj X))
    (hF : ∀ j, Function.Bijective (fun f : X ⟶ F j => T.map f)) :
    Function.Bijective (fun f : X ⟶ ∐ F => T.map f) :=
  ⟨criterionDerivedHom_coproduct_injective A D E T F X hX (fun j => (hF j).1),
    criterionDerivedHom_coproduct_surjective A D E T F X hTX (fun j => (hF j).2)⟩

omit [T.Additive]

/-- 始域の余積については、各因子でのHom比較の単射性だけを使う。 -/
lemma criterionDerivedHom_sourceCoproduct_injective (Y : DerivedModuleCategory A D)
    (hF : ∀ j, Function.Injective (fun f : F j ⟶ Y => T.map f)) :
    Function.Injective (fun f : ∐ F ⟶ Y => T.map f) := by
  intro f g hfg
  change T.map f = T.map g at hfg
  apply Sigma.hom_ext
  intro j
  apply hF j
  change T.map (Sigma.ι F j ≫ f) = T.map (Sigma.ι F j ≫ g)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, hfg]

/-- 始域の余積での全射性は、余積保存と各因子の全射性から得る。compact性は不要。 -/
lemma criterionDerivedHom_sourceCoproduct_surjective (Y : DerivedModuleCategory A D)
    [PreservesColimit (Discrete.functor F) T]
    (hF : ∀ j, Function.Surjective (fun f : F j ⟶ Y => T.map f)) :
    Function.Surjective (fun f : ∐ F ⟶ Y => T.map f) := by
  classical
  intro f
  let a (j : J) : F j ⟶ Y := (hF j (T.map (Sigma.ι F j) ≫ f)).choose
  have ha (j : J) : T.map (a j) = T.map (Sigma.ι F j) ≫ f :=
    (hF j (T.map (Sigma.ι F j) ≫ f)).choose_spec
  refine ⟨Sigma.desc a, ?_⟩
  apply (cancel_epi (sigmaComparison T F)).1
  apply Sigma.hom_ext
  intro j
  rw [ι_comp_sigmaComparison_assoc, ι_comp_sigmaComparison_assoc,
    ← CategoryTheory.Functor.map_comp, Sigma.ι_comp_desc, ha]

/-- 始域の余積でのHom比較の全単射性。生成族の直和のcompact性は要求しない。 -/
lemma criterionDerivedHom_sourceCoproduct_bijective (Y : DerivedModuleCategory A D)
    [PreservesColimit (Discrete.functor F) T]
    (hF : ∀ j, Function.Bijective (fun f : F j ⟶ Y => T.map f)) :
    Function.Bijective (fun f : ∐ F ⟶ Y => T.map f) :=
  ⟨criterionDerivedHom_sourceCoproduct_injective A D E T F Y (fun j => (hF j).1),
    criterionDerivedHom_sourceCoproduct_surjective A D E T F Y (fun j => (hF j).2)⟩

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionDerivedHomCoproducts

/-! ## CriterionDerivedHomTriangles（旧 SerrePositivity/DifferentialGraded/Morita/CriterionDerivedHomTriangles.lean） -/

/-! # Hom比較の終域変数における同型不変性と錐閉性

二つの実際のHom完全列を追う。右随伴・unit/counitは使わない。
-/

@[expose] public section CriterionDerivedHomTriangles
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Preadditive Pretriangulated
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)

/-- 終域の同型に沿ってHom比較の全単射性を運ぶ。 -/
lemma criterionDerivedHom_target_iso (X : DerivedModuleCategory A D)
    {Y Z : DerivedModuleCategory A D} (e : Y ≅ Z)
    (hZ : Function.Bijective (fun f : X ⟶ Z => T.map f)) :
    Function.Bijective (fun f : X ⟶ Y => T.map f) := by
  constructor
  · intro f g h
    change T.map f = T.map g at h
    apply (cancel_mono e.hom).1
    apply hZ.1
    change T.map (f ≫ e.hom) = T.map (g ≫ e.hom)
    rw [T.map_comp, T.map_comp, h]
  · intro f
    obtain ⟨g, hg⟩ := hZ.2 (f ≫ T.map e.hom)
    change T.map g = f ≫ T.map e.hom at hg
    refine ⟨g ≫ e.inv, ?_⟩
    change T.map (g ≫ e.inv) = f
    rw [T.map_comp, hg, Category.assoc, ← T.map_comp, e.hom_inv_id,
      T.map_id, Category.comp_id]

variable [T.CommShift ℤ] [T.IsTriangulated]

/-- 三角形の最初の二頂点とそのshiftでの比較から、第三頂点での全単射性を得る。 -/
lemma criterionDerivedHom_target_triangle
    (X : DerivedModuleCategory A D) (Δ : Triangle (DerivedModuleCategory A D))
    (hΔ : Δ ∈ distTriang (DerivedModuleCategory A D))
    (h1 : Function.Bijective (fun f : X ⟶ Δ.obj₁ => T.map f))
    (h2 : Function.Bijective (fun f : X ⟶ Δ.obj₂ => T.map f))
    (h1s : Function.Bijective (fun f : X ⟶ Δ.obj₁⟦(1 : ℤ)⟧ => T.map f))
    (h2s : Function.Bijective (fun f : X ⟶ Δ.obj₂⟦(1 : ℤ)⟧ => T.map f)) :
    Function.Bijective (fun f : X ⟶ Δ.obj₃ => T.map f) := by
  have hk (f : X ⟶ Δ.obj₃) (hf : T.map f = 0) : f = 0 := by
    have hz : f ≫ Δ.mor₃ = 0 := by
      apply h1s.1
      change T.map (f ≫ Δ.mor₃) = T.map 0
      rw [T.map_comp, hf, zero_comp, T.map_zero]
    obtain ⟨g, hg⟩ := Δ.coyoneda_exact₃ hΔ f hz
    have hzg : T.map g ≫ T.map Δ.mor₂ = 0 := by
      rw [← T.map_comp, ← hg, hf]
    obtain ⟨c, hc⟩ := (T.mapTriangle.obj Δ).coyoneda_exact₂
      (T.map_distinguished Δ hΔ) (T.map g) hzg
    obtain ⟨a, ha⟩ := h1.2 c
    change T.map a = c at ha
    have hga : g = a ≫ Δ.mor₁ := by
      apply h2.1
      change T.map g = T.map (a ≫ Δ.mor₁)
      rw [T.map_comp, ha]
      exact hc
    rw [hg, hga, Category.assoc, comp_distTriang_mor_zero₁₂ Δ hΔ, comp_zero]
  constructor
  · intro f g h
    apply sub_eq_zero.mp
    apply hk (f - g)
    change T.map f = T.map g at h
    rw [T.map_sub, h, sub_self]
  · intro f
    obtain ⟨a, ha⟩ := h1s.2 (f ≫ T.map Δ.mor₃)
    change T.map a = f ≫ T.map Δ.mor₃ at ha
    have hza : a ≫ Δ.mor₁⟦(1 : ℤ)⟧' = 0 := by
      apply h2s.1
      change T.map (a ≫ Δ.mor₁⟦(1 : ℤ)⟧') = T.map 0
      rw [T.map_comp, ha, Category.assoc, ← T.map_comp,
        comp_distTriang_mor_zero₃₁ Δ hΔ, T.map_zero, comp_zero, T.map_zero]
    obtain ⟨b, hb⟩ := Δ.coyoneda_exact₁ hΔ a hza
    have hdiff : (f - T.map b) ≫ (T.mapTriangle.obj Δ).mor₃ = 0 := by
      change (f - T.map b) ≫
        (T.map Δ.mor₃ ≫ (T.commShiftIso (1 : ℤ)).hom.app Δ.obj₁) = 0
      rw [← Category.assoc, sub_comp, ← T.map_comp, ← hb, ha, sub_self, zero_comp]
    obtain ⟨c, hc⟩ := (T.mapTriangle.obj Δ).coyoneda_exact₃
      (T.map_distinguished Δ hΔ) (f - T.map b) hdiff
    obtain ⟨d, hd⟩ := h2.2 c
    change T.map d = c at hd
    refine ⟨b + d ≫ Δ.mor₂, ?_⟩
    change T.map (b + d ≫ Δ.mor₂) = f
    rw [T.map_add, T.map_comp, hd]
    change f - T.map b = c ≫ T.map Δ.mor₂ at hc
    rw [← hc]
    exact add_sub_cancel _ _

/-- 零対象を終域に持つHom比較は全単射。 -/
lemma criterionDerivedHom_target_isZero (X : DerivedModuleCategory A D)
    {Y : DerivedModuleCategory A D} (hY : IsZero Y) :
    Function.Bijective (fun f : X ⟶ Y => T.map f) := by
  constructor
  · intro f g _
    exact hY.eq_of_tgt f g
  · intro f
    exact ⟨0, (T.map_isZero hY).eq_of_tgt _ _⟩

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionDerivedHomTriangles

/-! ## CriterionDerivedHomLocus（旧 SerrePositivity/DifferentialGraded/Morita/CriterionDerivedHomLocus.lean） -/

/-! # 全shiftでのHom比較の全単射性が定める局所化帰納の対象クラス -/

@[expose] public section CriterionDerivedHomLocus
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Pretriangulated ZeroObject
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  (X : DerivedModuleCategory A D)

/-- 固定した始域から全整数shiftへの実際のHom比較が全単射となる終域。 -/
def criterionDerivedHomTargetLocus : ObjectProperty (DerivedModuleCategory A D) :=
  fun Y => ∀ n : ℤ, Function.Bijective (fun f : X ⟶ Y⟦n⟧ => T.map f)

lemma criterionDerivedHomTargetLocus_shift {Y : DerivedModuleCategory A D}
    (hY : criterionDerivedHomTargetLocus A D E T X Y) (a : ℤ) :
    criterionDerivedHomTargetLocus A D E T X (Y⟦a⟧) := by
  intro b
  exact criterionDerivedHom_target_iso A D E T X
    ((shiftFunctorAdd _ a b).app Y).symm (hY (a + b))

instance criterionDerivedHomTargetLocusClosedIso :
    (criterionDerivedHomTargetLocus A D E T X).IsClosedUnderIsomorphisms where
  of_iso e hY n := criterionDerivedHom_target_iso A D E T X
    ((shiftFunctor _ n).mapIso e.symm) (hY n)

instance criterionDerivedHomTargetLocusShift :
    (criterionDerivedHomTargetLocus A D E T X).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun _ hY => criterionDerivedHomTargetLocus_shift A D E T X hY a⟩

variable [T.CommShift ℤ] [T.IsTriangulated]

instance criterionDerivedHomTargetLocusClosedTriangle :
    (criterionDerivedHomTargetLocus A D E T X).IsTriangulatedClosed₃ := by
  apply ObjectProperty.IsTriangulatedClosed₃.mk'
  intro Δ hΔ h1 h2 n
  apply criterionDerivedHom_target_triangle A D E T X _
    (Triangle.shift_distinguished Δ hΔ n) (h1 n) (h2 n)
  · exact (criterionDerivedHomTargetLocus_shift A D E T X h1 n) 1
  · exact (criterionDerivedHomTargetLocus_shift A D E T X h2 n) 1

instance criterionDerivedHomTargetLocusTriangulated :
    (criterionDerivedHomTargetLocus A D E T X).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, fun n =>
    criterionDerivedHom_target_isZero A D E T X ((shiftFunctor _ n).map_isZero (isZero_zero _))⟩
  toIsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

/-- 各compact生成元とそのcompactな像に対するHom比較の対象クラスは、余積で閉じる。 -/
lemma criterionDerivedHomTargetLocus_coproduct
    (hcop : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) T)
    (hX : moduleCompact A D X) (hTX : moduleCompact A E (T.obj X))
    (J : Type u) (F : J → DerivedModuleCategory A D)
    (hF : ∀ j, criterionDerivedHomTargetLocus A D E T X (F j)) :
    criterionDerivedHomTargetLocus A D E T X (∐ F) := by
  intro n
  let := hcop J
  apply criterionDerivedHom_target_iso A D E T X
    (PreservesCoproduct.iso (shiftFunctor _ n) F)
  exact criterionDerivedHom_coproduct_bijective A D E T (fun j => (F j)⟦n⟧) X
    hX hTX (fun j => hF j n)

end SerrePositivity.DifferentialGraded.Morita
end

end CriterionDerivedHomLocus
