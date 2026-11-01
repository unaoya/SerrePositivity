module

public import SerrePositivity.DifferentialGraded.Morita.Kernel
public import SerrePositivity.DifferentialGraded.Module.RestrictionEnriched
public import SerrePositivity.DifferentialGraded.Endomorphism.Derived.Functors
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Triangulated.Functor
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import SerrePositivity.DifferentialGraded.Endomorphism.Scalar.EnhancementComparison
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionRepresentable
public import SerrePositivity.DifferentialGraded.Derived.RightTensor
public import SerrePositivity.DifferentialGraded.Derived.EvaluationTriangles
public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import SerrePositivity.DifferentialGraded.Derived.RightTensorLeftFunctor
public import SerrePositivity.DifferentialGraded.Endomorphism.Derived.Adjunction
public import SerrePositivity.DifferentialGraded.Morita.CoherenceCompositionKernel
public import SerrePositivity.DifferentialGraded.Morita.CoherenceAssociator

/-!
# Morita.Perfect

## 概要
13 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## AdjunctionHom（旧 SerrePositivity/DifferentialGraded/Morita/AdjunctionHom.lean） -/

/-! # 任意kernelの通常Hom dg関手

## 概要
右E・左D kernel Pに対し、Hom_E(P(d),N)を値とする右D加群を全Hom自然に構成する。

## 方針
大きい加群dg圏上の代表加群をPに沿って制限し、パラメータ付きYoneda作用を引き戻す。

## 規約と注意
全右E加群型のSmallは仮定しない。Homの局所K-flat性・kernelの射影性も不要。
これは通常Homであり、一般の導来右随伴の構成とは区別する。

## 使われ方
U16aの一般kernelのtensor–Hom随伴と右導来化の基礎。
-/

@[expose] public section AdjunctionHom
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- kernelに沿って大きい加群dg圏の代表加群を制限する。 -/
def kernelHomModule (N : RightModule A E) : RightModule A D :=
  restrictModule A D (RightModule A E) P.toFunctor.op (representable A N)

/-- 通常Homの後合成を、全Hom自然なパラメータ付き族として定義する。 -/
def kernelHomParam (M N : RightModule A E) :
    ModuleParamTrans A D (moduleHom A E M N)
      (kernelHomModule A D E P M) (kernelHomModule A D E P N) :=
  moduleRestrictionParam A D (RightModule A E) P.toFunctor.op
    (yonedaExtension A M (representable A N) (𝟙 _))

/-- 任意kernelの通常Hom dg関手。大きい全加群型のSmallは不要。 -/
def kernelHom : DGFunctor A (RightModule A E) (RightModule A D) :=
  (Bimodule.ofParamTrans A D (RightModule A E) (kernelHomModule A D E P)
    (kernelHomParam A D E P)
    (by
      intro N d
      change eId (Complex A) N ≫
        yonedaExtensionApp A N (representable A N) (𝟙 _) (op (P.rightAt d.unop)) = _
      rw [endomorphismYonedaApp]
      exact (leftRepresentable A (P.rightAt d.unop)).map_id N)
    (by
      intro M N T d
      change eComp (Complex A) M N T ≫
        yonedaExtensionApp A M (representable A T) (𝟙 _) (op (P.rightAt d.unop)) =
        (yonedaExtensionApp A M (representable A N) (𝟙 _) (op (P.rightAt d.unop)) ⊗ₘ
          yonedaExtensionApp A N (representable A T) (𝟙 _) (op (P.rightAt d.unop))) ≫
          enrichedComposition _ _ _
      rw [endomorphismYonedaApp, endomorphismYonedaApp, endomorphismYonedaApp]
      exact (leftRepresentable A (P.rightAt d.unop)).map_comp M N T)).toFunctor

/-- 通常Hom関手の値は元の全Hom endそのもの。 -/
lemma kernelHom_value (N : RightModule A E) (d : D) :
    ((kernelHom A D E P).obj N).obj (op d) = moduleHom A E (P.rightAt d) N := rfl

/-- 通常Hom関手の全Hom mapは、各列からの共変representableのmapに一致する。 -/
lemma kernelHom_map_π (M N : RightModule A E) (d : D) :
    (kernelHom A D E P).map M N ≫
        moduleHomπ A D ((kernelHom A D E P).obj M) ((kernelHom A D E P).obj N) d =
      (leftRepresentable A (P.rightAt d)).map M N := by
  change (moduleHomEquiv A D _ _ _).symm (kernelHomParam A D E P M N) ≫
    moduleHomπ A D (kernelHomModule A D E P M) (kernelHomModule A D E P N) d = _
  rw [moduleHomEquiv_symm_π]
  exact endomorphismYonedaApp A (RightModule A E) (P.rightAt d) M N

/-- 通常Homの閉零射の評価は、元の全Hom endの後合成射。 -/
lemma kernelHom_map_eval {M N : ModuleCategory A E} (f : M ⟶ N) (d : D) :
    (moduleEvaluation A D d).map ((kernelHom A D E P).onClosed.map f) =
      eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) (P.rightAt d)) f := by
  let M₀ := ForgetEnrichment.to (Complex A) M
  let N₀ := ForgetEnrichment.to (Complex A) N
  calc
    _ = (moduleEvaluation A (EndomorphismObject (P.rightAt d)) .point).map
        ((endomorphismModuleHom A E (P.rightAt d)).onClosed.map f) := by
      apply Cochain.ofHom_injective
      rw [moduleEvaluation_cochain, moduleEvaluation_cochain]
      change (moduleHomπ A D _ _ d).f 0
          (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f ≫
            (kernelHom A D E P).map M₀ N₀)).val =
        (moduleHomπ A (EndomorphismObject (P.rightAt d)) _ _ .point).f 0
          (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f ≫
            (endomorphismModuleHom A E (P.rightAt d)).map M₀ N₀)).val
      rw [cycleFromUnit_postcomp, cycleFromUnit_postcomp]
      have h := (kernelHom_map_π A D E P M₀ N₀ d).trans
        (endomorphismModuleHom_map_π A E (P.rightAt d) M₀ N₀).symm
      exact congrArg (fun k => k.f 0 (cycleFromUnit _
        (ForgetEnrichment.homTo (Complex A) f)).val) h
    _ = _ := endomorphismModuleHom_map_eval A E (P.rightAt d) M₀ N₀ f .point

end SerrePositivity.DifferentialGraded.Morita
end

end AdjunctionHom

/-! ## AdjunctionBrownSeed（旧 SerrePositivity/DifferentialGraded/Morita/AdjunctionBrownSeed.lean） -/

/-! # 導来右随伴の表現対象を構成する初期生成元被覆

## 概要
余積を保つ指定関手Lと終域対象Yに対し、全ての生成元からのL像の射を初期対象で表す。

## 方針
局所小性で全射の添字をuへ縮小し、代表加群の整数shiftの余積と比較同型を使う。

## 規約と注意
指定した余積の保存を明示する。随伴の存在や表現可能性は仮定しない。
これは初期被覆であり、関係を消す段階と極限での表現可能性の証明は後続の仕事。

## 使われ方
U16aの一般kernelの右随伴を、compact生成元から引用なしに構成するための初期段階。
-/

@[expose] public section AdjunctionBrownSeed
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (L : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  (Y : DerivedModuleCategory A E)

/-- 全てのshiftした代表加群のL像からYへの射。 -/
def brownSeedRawIndex := Σ p : D × ℤ, L.obj (moduleCompactGenerators A D p) ⟶ Y

/-- 生成元の添字と局所小性から、全射の添字は係数・Hom宇宙uでsmall。 -/
instance brownSeedRawIndexSmall : Small.{u} (brownSeedRawIndex A D E L Y) := by
  dsimp only [brownSeedRawIndex]
  infer_instance

/-- u-smallな実際の余積添字。 -/
abbrev brownSeedIndex := Shrink.{u} (brownSeedRawIndex A D E L Y)

/-- 初期被覆に使う生成元の族。 -/
def brownSeedFamily (i : brownSeedIndex A D E L Y) : DerivedModuleCategory A D :=
  moduleCompactGenerators A D (((equivShrink (brownSeedRawIndex A D E L Y)).symm i).1)

/-- 各生成元のL像からYへの、添字そのものが指定する射。 -/
def brownSeedArrow (i : brownSeedIndex A D E L Y) :
    L.obj (brownSeedFamily A D E L Y i) ⟶ Y :=
  ((equivShrink (brownSeedRawIndex A D E L Y)).symm i).2

/-- 初期被覆の源はu-smallな生成元余積。 -/
def brownSeed : DerivedModuleCategory A D := ∐ brownSeedFamily A D E L Y

/-- 初期被覆のL像からYへの射。余積比較を反転して構成する。 -/
def brownSeedMap [PreservesColimit (Discrete.functor (brownSeedFamily A D E L Y)) L] :
    L.obj (brownSeed A D E L Y) ⟶ Y :=
  (PreservesCoproduct.iso L (brownSeedFamily A D E L Y)).hom ≫
    Sigma.desc (brownSeedArrow A D E L Y)

variable [PreservesColimit (Discrete.functor (brownSeedFamily A D E L Y)) L]

/-- 初期被覆の各成分の像は、指定した元の射そのもの。 -/
lemma brownSeedMap_ι (i : brownSeedIndex A D E L Y) :
    L.map (Sigma.ι (brownSeedFamily A D E L Y) i) ≫ brownSeedMap A D E L Y =
      brownSeedArrow A D E L Y i := by
  dsimp only [brownSeedMap]
  rw [← ι_comp_sigmaComparison L (brownSeedFamily A D E L Y) i,
    ← PreservesCoproduct.inv_hom L (brownSeedFamily A D E L Y), Category.assoc,
    Iso.inv_hom_id_assoc, Sigma.ι_comp_desc]

/-- 各compact生成元のL像からの任意の射は、初期被覆のL像を経由する。 -/
lemma brownSeedMap_generator_surjective (p : D × ℤ)
    (f : L.obj (moduleCompactGenerators A D p) ⟶ Y) :
    ∃ g : moduleCompactGenerators A D p ⟶ brownSeed A D E L Y,
      L.map g ≫ brownSeedMap A D E L Y = f := by
  let T := brownSeedRawIndex A D E L Y
  let good : T → Prop := fun r =>
    ∃ g : moduleCompactGenerators A D r.1 ⟶ brownSeed A D E L Y,
      L.map g ≫ brownSeedMap A D E L Y = r.2
  obtain ⟨i, hi⟩ := (equivShrink T).symm.surjective (⟨p, f⟩ : T)
  have h : good ((equivShrink T).symm i) :=
    ⟨Sigma.ι (brownSeedFamily A D E L Y) i, brownSeedMap_ι A D E L Y i⟩
  rw [hi] at h
  exact h

end SerrePositivity.DifferentialGraded.Morita
end

end AdjunctionBrownSeed

/-! ## AdjunctionBrownRelations（旧 SerrePositivity/DifferentialGraded/Morita/AdjunctionBrownRelations.lean） -/

/-! # 表現対象の近似における生成元の全関係

## 概要
指定した射L(X)→Yについて、生成元から来てその像が零になる射を一つの余積からの射にまとめる。

## 方針
局所小性で関係の添字をuへ縮小する。指定余積の保存からL像が零になることを証明する。

## 規約と注意
随伴の存在は仮定しない。関係を消すconeは次の段階で構成する。

## 使われ方
U16aの一般右随伴の表現対象を構成する、初期被覆からの後続段階の入力。
-/

@[expose] public section AdjunctionBrownRelations
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (L : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  {X : DerivedModuleCategory A D} {Y : DerivedModuleCategory A E} (r : L.obj X ⟶ Y)

/-- 生成元からXに来て、rの下で零になる全ての射。 -/
def brownRelationRawIndex :=
  Σ p : D × ℤ, {f : moduleCompactGenerators A D p ⟶ X // L.map f ≫ r = 0}

/-- 既存の局所小性により、全関係の添字もu-small。 -/
instance brownRelationRawIndexSmall : Small.{u} (brownRelationRawIndex A D E L r) := by
  dsimp only [brownRelationRawIndex]
  infer_instance

/-- u-smallな関係の実際の添字。 -/
abbrev brownRelationIndex := Shrink.{u} (brownRelationRawIndex A D E L r)

/-- 各関係の源となる生成元。 -/
def brownRelationFamily (i : brownRelationIndex A D E L r) : DerivedModuleCategory A D :=
  moduleCompactGenerators A D (((equivShrink (brownRelationRawIndex A D E L r)).symm i).1)

/-- 各関係をXへの射として取り出す。 -/
def brownRelationArrow (i : brownRelationIndex A D E L r) :
    brownRelationFamily A D E L r i ⟶ X :=
  ((equivShrink (brownRelationRawIndex A D E L r)).symm i).2.val

/-- 各関係のL像とrの合成は零。 -/
lemma brownRelationArrow_condition (i : brownRelationIndex A D E L r) :
    L.map (brownRelationArrow A D E L r i) ≫ r = 0 :=
  ((equivShrink (brownRelationRawIndex A D E L r)).symm i).2.property

/-- 全関係の源は生成元のu-small余積。 -/
def brownRelationObject : DerivedModuleCategory A D := ∐ brownRelationFamily A D E L r

/-- 全関係をまとめたXへの射。 -/
def brownRelationMap : brownRelationObject A D E L r ⟶ X :=
  Sigma.desc (brownRelationArrow A D E L r)

/-- 関係の包含からの合成は元の関係を計算する。 -/
lemma brownRelationMap_ι (i : brownRelationIndex A D E L r) :
    Sigma.ι (brownRelationFamily A D E L r) i ≫ brownRelationMap A D E L r =
      brownRelationArrow A D E L r i := Sigma.ι_comp_desc _ _

/-- 関係余積の保存により、全関係の射のL像もrで零になる。 -/
lemma brownRelationMap_image_zero
    [PreservesColimit (Discrete.functor (brownRelationFamily A D E L r)) L] :
    L.map (brownRelationMap A D E L r) ≫ r = 0 := by
  apply (isColimitOfHasCoproductOfPreservesColimit L
    (brownRelationFamily A D E L r)).hom_ext
  rintro ⟨i⟩
  change L.map (Sigma.ι (brownRelationFamily A D E L r) i) ≫
    (L.map (brownRelationMap A D E L r) ≫ r) =
    L.map (Sigma.ι (brownRelationFamily A D E L r) i) ≫ 0
  rw [← Category.assoc, ← Functor.map_comp, brownRelationMap_ι, comp_zero]
  exact brownRelationArrow_condition A D E L r i

/-- 全関係の射を殺すXからの射は、rに関する生成元からの任意の関係を殺す。 -/
lemma brownRelationMap_kills {Z : DerivedModuleCategory A D} (g : X ⟶ Z)
    (hg : brownRelationMap A D E L r ≫ g = 0) (p : D × ℤ)
    (f : moduleCompactGenerators A D p ⟶ X) (hf : L.map f ≫ r = 0) : f ≫ g = 0 := by
  let T := brownRelationRawIndex A D E L r
  let good : T → Prop := fun t => t.2.val ≫ g = 0
  obtain ⟨i, hi⟩ := (equivShrink T).symm.surjective (⟨p, ⟨f, hf⟩⟩ : T)
  have h : brownRelationArrow A D E L r i ≫ g = 0 := by
    rw [← brownRelationMap_ι A D E L r i, Category.assoc, hg, comp_zero]
  change good ((equivShrink T).symm i) at h
  rw [hi] at h
  exact h

end SerrePositivity.DifferentialGraded.Morita
end

end AdjunctionBrownRelations

/-! ## AdjunctionBrownSuccessor（旧 SerrePositivity/DifferentialGraded/Morita/AdjunctionBrownSuccessor.lean） -/

/-! # 生成元の関係を消す表現対象近似の後続段階

## 概要
射L(X)→Yを、全ての生成元の関係を殺すX→X'に沿って延長する。

## 方針
全関係の余積からの射をdistinguished三角形に補完し、L像のHom完全性で延長射を得る。

## 規約と注意
Lの三角性と指定余積の保存を明示する。随伴の存在や表現可能性は仮定しない。

## 使われ方
U16aの一般右随伴を、初期被覆から可算telescopeへ構成するための後続操作。
-/

@[expose] public section AdjunctionBrownSuccessor
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (L : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  {X : DerivedModuleCategory A D} {Y : DerivedModuleCategory A E} (r : L.obj X ⟶ Y)

/-- 同じ標的射を延長し、生成元から来る全関係を消す一つの後続段階。 -/
structure BrownSuccessor where
  obj : DerivedModuleCategory A D
  map : X ⟶ obj
  target : L.obj obj ⟶ Y
  fac : L.map map ≫ target = r
  kills : ∀ (p : D × ℤ) (f : moduleCompactGenerators A D p ⟶ X),
    L.map f ≫ r = 0 → f ≫ map = 0

variable [L.CommShift ℤ] [L.IsTriangulated]
  [PreservesColimit (Discrete.functor (brownRelationFamily A D E L r)) L]

/-- 三角形の補完とL像のHom完全性から、関係を消す後続段階が存在する。 -/
lemma brownSuccessor_nonempty : Nonempty (BrownSuccessor A D E L r) := by
  obtain ⟨Z, a, b, hT⟩ := distinguished_cocone_triangle (brownRelationMap A D E L r)
  let T := Triangle.mk (brownRelationMap A D E L r) a b
  have hL := L.map_distinguished T hT
  obtain ⟨r', hr'⟩ := (L.mapTriangle.obj T).yoneda_exact₂ hL r
    (brownRelationMap_image_zero A D E L r)
  refine ⟨⟨Z, a, r', hr'.symm, ?_⟩⟩
  intro p f hf
  exact brownRelationMap_kills A D E L r a (comp_distTriang_mor_zero₁₂ T hT) p f hf

/-- 証明付きの後続操作を一つ選ぶ。 -/
def brownSuccessor : BrownSuccessor A D E L r :=
  Classical.choice (brownSuccessor_nonempty A D E L r)

/-- 後続操作は元の標的射を延長する。 -/
lemma brownSuccessor_fac :
    L.map (brownSuccessor A D E L r).map ≫ (brownSuccessor A D E L r).target = r :=
  (brownSuccessor A D E L r).fac

/-- 後続操作は、元の標的射の下で零になる生成元からの任意射を消す。 -/
lemma brownSuccessor_kills (p : D × ℤ) (f : moduleCompactGenerators A D p ⟶ X)
    (hf : L.map f ≫ r = 0) : f ≫ (brownSuccessor A D E L r).map = 0 :=
  (brownSuccessor A D E L r).kills p f hf

end SerrePositivity.DifferentialGraded.Morita
end

end AdjunctionBrownSuccessor

/-! ## PerfectFunctoriality（旧 SerrePositivity/DifferentialGraded/Morita/PerfectFunctoriality.lean） -/

/-! # U16d：主Perfへの実際の制限の関手性

kernel作用を主Perfへ制限する際のアダプタ。保存条件を明示し、未実装のkernel作用を仮定しない。
通常の完全充満部分圏のliftを再利用して、射・自然変換・合成の比較を保持する。
-/

@[expose] public section PerfectFunctoriality
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

lemma perfectFunctor_of_generators (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    [T.CommShift ℤ] [T.IsTriangulated]
    (hgen : ∀ d : D, modulePerfect A E (T.obj ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A d)))))
    {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    modulePerfect A E (T.obj X) := by
  let P := (modulePerfect A E).inverseImage T
  have : P.IsTriangulated := by dsimp [P]; infer_instance
  have : P.IsClosedUnderIsomorphisms := by dsimp [P]; infer_instance
  have : P.IsStableUnderRetracts :=
    ⟨fun r hY => (modulePerfect A E).prop_of_retract (r.map T) hY⟩
  exact ((modulePerfect_le_iff_generators A D P).2 hgen) X hX

def perfectFunctorRestriction (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X)) :
    PerfectModuleCategory A D ⥤ PerfectModuleCategory A E :=
  (modulePerfect A E).lift (perfectModuleInclusion A D Set.univ ⋙ T)
    (fun X => hT X.obj X.property)

def perfectFunctorInclusionIso (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X)) :
    perfectFunctorRestriction A D E T hT ⋙ perfectModuleInclusion A E Set.univ ≅
      perfectModuleInclusion A D Set.univ ⋙ T := Iso.refl _

def perfectFunctorTransformation
    (T U : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    (hU : ∀ X, modulePerfect A D X → modulePerfect A E (U.obj X)) (α : T ⟶ U) :
    perfectFunctorRestriction A D E T hT ⟶ perfectFunctorRestriction A D E U hU where
  app X := ObjectProperty.homMk (α.app X.obj)
  naturality _ _ f := (modulePerfect A E).hom_ext (α.naturality f.hom)

lemma perfectFunctorTransformation_id
    (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X)) :
    perfectFunctorTransformation A D E T T hT hT (𝟙 T) = 𝟙 _ := rfl

lemma perfectFunctorTransformation_comp
    (T U V : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    (hU : ∀ X, modulePerfect A D X → modulePerfect A E (U.obj X))
    (hV : ∀ X, modulePerfect A D X → modulePerfect A E (V.obj X))
    (α : T ⟶ U) (β : U ⟶ V) :
    perfectFunctorTransformation A D E T V hT hV (α ≫ β) =
      perfectFunctorTransformation A D E T U hT hU α ≫
        perfectFunctorTransformation A D E U V hU hV β := rfl

def perfectFunctorIso
    (T U : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    (hU : ∀ X, modulePerfect A D X → modulePerfect A E (U.obj X)) (e : T ≅ U) :
    perfectFunctorRestriction A D E T hT ≅ perfectFunctorRestriction A D E U hU :=
  NatIso.ofComponents (fun X => (modulePerfect A E).isoMk (e.app X.obj))
    (by intro X Y f; exact (modulePerfect A E).hom_ext (e.hom.naturality f.hom))

def perfectFunctorIdentityIso :
    perfectFunctorRestriction A D D (𝟭 _) (fun _ h => h) ≅ 𝟭 (PerfectModuleCategory A D) :=
  Iso.refl _

variable (B : Type z) [DGCategory A B] [Small.{u} B]

def perfectFunctorCompositionIso
    (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (U : DerivedModuleCategory A E ⥤ DerivedModuleCategory A B)
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    (hU : ∀ X, modulePerfect A E X → modulePerfect A B (U.obj X)) :
    perfectFunctorRestriction A D E T hT ⋙ perfectFunctorRestriction A E B U hU ≅
      perfectFunctorRestriction A D B (T ⋙ U) (fun X h => hU _ (hT X h)) := Iso.refl _

lemma perfectFunctorComposition_naturality
    (T T' : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    (U U' : DerivedModuleCategory A E ⥤ DerivedModuleCategory A B)
    (hT : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    (hT' : ∀ X, modulePerfect A D X → modulePerfect A E (T'.obj X))
    (hU : ∀ X, modulePerfect A E X → modulePerfect A B (U.obj X))
    (hU' : ∀ X, modulePerfect A E X → modulePerfect A B (U'.obj X))
    (α : T ⟶ T') (β : U ⟶ U') :
    NatTrans.hcomp (perfectFunctorTransformation A D E T T' hT hT' α)
        (perfectFunctorTransformation A E B U U' hU hU' β) ≫
        (perfectFunctorCompositionIso A D E B T' U' hT' hU').hom =
      (perfectFunctorCompositionIso A D E B T U hT hU).hom ≫
        perfectFunctorTransformation A D B (T ⋙ U) (T' ⋙ U')
          (fun X h => hU _ (hT X h)) (fun X h => hU' _ (hT' X h)) (NatTrans.hcomp α β) := by
  simp only [perfectFunctorCompositionIso, Iso.refl_hom, Category.comp_id, Category.id_comp]
  apply NatTrans.ext
  funext X
  apply (modulePerfect A B).hom_ext
  simp only [NatTrans.hcomp_app]
  change β.app (T.obj X.obj) ≫ U'.map (α.app X.obj) = (NatTrans.hcomp α β).app X.obj
  exact (NatTrans.hcomp_app α β X.obj).symm

end SerrePositivity.DifferentialGraded.Morita
end

end PerfectFunctoriality

/-! ## PerfectKernelImage（旧 SerrePositivity/DifferentialGraded/Morita/PerfectKernelImage.lean） -/

/-! # U16d：通常kernelの各列のperfect性から実際の主Perf作用を構成する

入力の射影解像度と主導来retractの射の計算を使う。kernelの射影性やlocalHomKFlatは追加しない。
-/

@[expose] public section PerfectKernelImage
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

lemma perfectDGFunctorImage_finiteCell
    (T : DGFunctor A (RightModule A D) (RightModule A E))
    (hgen : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
      (T.onClosed.obj (ForgetEnrichment.of (Complex A) (representable A d)))))
    {M : ModuleCategory A D} (hM : moduleFiniteCell A D M) :
    modulePerfect A E ((moduleToDerived A E).obj (T.onClosed.obj M)) := by
  let F := T.onClosed
  let Q := moduleToDerived A E
  let G := F ⋙ Q
  let P := modulePerfect A E
  let : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBiproducts G
  obtain ⟨c⟩ := hM
  induction c with
  | zero => exact P.prop_of_isZero (Q.map_isZero (F.map_isZero (moduleZero_isZero A D)))
  | generator d _ => exact hgen d
  | @shift M n c ih =>
      exact P.prop_of_iso
        (Q.mapIso (dgModuleFunctorShiftIso A E D T n
          (ForgetEnrichment.to (Complex A) M)) ≪≫ (Q.commShiftIso n).app (F.obj M)).symm
        (P.le_shift n _ ih)
  | @sum M N c d ihc ihd =>
      exact P.prop_of_iso
        (G.mapIso (moduleBiprodIso A D M N) ≪≫ G.mapBiprod M N ≪≫
          biprod.isoProd (G.obj M) (G.obj N)).symm (P.prop_prod _ _ ihc ihd)
  | @cone M N c d f ihc ihd =>
      exact P.prop_of_iso (Q.mapIso (dgModuleFunctorConeIso A D E T f))
        (P.ext_of_isTriangulatedClosed₃ (moduleDerivedConeTriangle A E (F.map f))
          (moduleDerivedConeTriangle_distinguished A E (F.map f)) ihc ihd)
  | iso c e ih => exact P.prop_of_iso (G.mapIso e) ih

lemma perfectDGFunctorImage_projectivePerfect
    (T : DGFunctor A (RightModule A D) (RightModule A E))
    (hgen : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
      (T.onClosed.obj (ForgetEnrichment.of (Complex A) (representable A d)))))
    {M : ModuleCategory A D} (hM : moduleHomotopicallyProjective A D M)
    (hPerf : modulePerfect A D ((moduleToDerived A D).obj M)) :
    modulePerfect A E ((moduleToDerived A E).obj (T.onClosed.obj M)) := by
  let F := T.onClosed
  let Q := moduleToHomotopy A D
  let Q' := moduleToHomotopy A E
  obtain ⟨N, hN, ⟨a⟩⟩ := (modulePerfect_iff A D _).1 hPerf
  have hNP := moduleFiniteCellOver_homotopicallyProjective A D hN
  obtain ⟨i, hi⟩ := moduleProjectiveToDerived_map_surjective A D hM a.i
  obtain ⟨r, hr⟩ := moduleProjectiveToDerived_map_surjective A D hNP a.r
  have h : Q.map (i ≫ r) = Q.map (𝟙 M) := by
    apply (moduleProjectiveDerivedHomEquiv A D hM M).injective
    rw [moduleProjectiveDerivedHomEquiv_map, moduleProjectiveDerivedHomEquiv_map,
      Functor.map_comp, hi, hr, a.retract, CategoryTheory.Functor.map_id]
  let b : Retract (Q'.obj (F.obj M)) (Q'.obj (F.obj N)) :=
    { i := Q'.map (F.map i)
      r := Q'.map (F.map r)
      retract := by
        have he := congrArg T.onHomotopy.map h
        change Q'.map (F.map (i ≫ r)) = Q'.map (F.map (𝟙 M)) at he
        simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using he }
  let L := moduleHomotopyToDerivedClosed A E
  let e := moduleToHomotopyDerivedIso A E
  exact modulePerfectOver_of_retract A E
    ((Retract.ofIso (e.app (F.obj M)).symm).trans
      ((b.map L).trans (Retract.ofIso (e.app (F.obj N)))))
    (perfectDGFunctorImage_finiteCell A D E T hgen hN)

variable (P : Bimodule A E D)
  (hP : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
    (ForgetEnrichment.of (Complex A) (P.rightAt d))))

include hP

lemma perfectKernelImage_representable (d : D) :
    modulePerfect A E ((moduleToDerived A E).obj
      ((kernelTensor A D E P).onClosed.obj
        (ForgetEnrichment.of (Complex A) (representable A d)))) :=
  (modulePerfect A E).prop_of_iso
    ((moduleToDerived A E).mapIso (BimoduleTensor.rightUnitIso A E D P d)).symm (hP d)

lemma perfectKernelAction_preserves {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    modulePerfect A E ((kernelDerivedTensorOnBimodule A D E P).obj X) := by
  obtain ⟨⟨M⟩⟩ := X
  let R := moduleCanonicalProjectiveResolution A D M
  have hR : modulePerfect A D ((moduleToDerived A D).obj R.obj) :=
    (modulePerfect A D).prop_of_iso (moduleDerivedIso A D R.π R.quasiIso).symm hX
  exact (modulePerfect A E).prop_of_iso
    (kernelDerivedTensorOnBimoduleComputation A D E P R).symm
    (perfectDGFunctorImage_projectivePerfect A D E (kernelTensor A D E P)
      (perfectKernelImage_representable A D E P hP) R.projective hR)

def perfectKernelAction : PerfectModuleCategory A D ⥤ PerfectModuleCategory A E :=
  perfectFunctorRestriction A D E (kernelDerivedTensorOnBimodule A D E P)
    (fun _ h => perfectKernelAction_preserves A D E P hP h)

def perfectKernelActionInclusionIso :
    perfectKernelAction A D E P hP ⋙ perfectModuleInclusion A E Set.univ ≅
      perfectModuleInclusion A D Set.univ ⋙ kernelDerivedTensorOnBimodule A D E P := Iso.refl _

end SerrePositivity.DifferentialGraded.Morita
end

end PerfectKernelImage

/-! ## PerfectKernelColumns（旧 SerrePositivity/DifferentialGraded/Morita/PerfectKernelColumns.lean） -/

/-! # 主導来kernelの列のperfect性と、kernelの全導来射に自然なPerf作用

列の評価自体を指定主局所化へ降ろし、通常kernelの代表によらない条件を使う。
U16aの実際の作用関手から主Perfへの制限を構成し、恒等・合成も保つ。
-/

@[expose] public section PerfectKernelColumns
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

def kernelDerivedColumn (d : D) : Kernel A D E ⥤ DerivedModuleCategory A E :=
  bimoduleDerivedLift A E D (BimoduleCategory.evaluation A E D d ⋙ moduleToDerived A E)
    (fun _ _ f hf => moduleToDerived_inverts A E ((BimoduleCategory.evaluation A E D d).map f)
      (BimoduleCategory.quasiIso_evaluation A E D hf d))

lemma kernelDerivedColumn_fac (d : D) :
    bimoduleToDerived A E D ⋙ kernelDerivedColumn A D E d =
      BimoduleCategory.evaluation A E D d ⋙ moduleToDerived A E :=
  bimoduleDerivedLift_fac A E D _ _

def kernelDerivedColumnComputation (d : D) (P : BimoduleCategory A E D) :
    (kernelDerivedColumn A D E d).obj ((bimoduleToDerived A E D).obj P) ≅
      (moduleToDerived A E).obj ((BimoduleCategory.evaluation A E D d).obj P) :=
  (eqToIso (kernelDerivedColumn_fac A D E d)).app P

def kernelColumnsPerfect : ObjectProperty (Kernel A D E) :=
  fun K => ∀ d : D, modulePerfect A E ((kernelDerivedColumn A D E d).obj K)

lemma kernelColumnsPerfect_ofBimodule_iff (P : BimoduleCategory A E D) :
    kernelColumnsPerfect A D E ((bimoduleToDerived A E D).obj P) ↔
      ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
        (ForgetEnrichment.of (Complex A) ((BimoduleCategory.underlying A E D P).rightAt d))) := by
  constructor
  · intro h d
    exact (modulePerfect A E).prop_of_iso (kernelDerivedColumnComputation A D E d P) (h d)
  · intro h d
    exact (modulePerfect A E).prop_of_iso (kernelDerivedColumnComputation A D E d P).symm (h d)

variable [Small.{u} D]

def kernelDerivedColumnActionIso (K : Kernel A D E) (d : D) :
    (kernelDerivedTensor A D E K).obj
        ((moduleToDerived A D).obj (ForgetEnrichment.of (Complex A) (representable A d))) ≅
      (kernelDerivedColumn A D E d).obj K := by
  obtain ⟨⟨P⟩⟩ := K
  let M := ForgetEnrichment.of (Complex A) (representable A d)
  let R := moduleIdentityProjectiveResolution A D M (representable_homotopicallyProjective A D d)
  exact (kernelDerivedTensorOnBimoduleIso A D E P).app ((moduleToDerived A D).obj M) ≪≫
    kernelDerivedTensorOnBimoduleComputation A D E (BimoduleCategory.underlying A E D P) R ≪≫
    (moduleToDerived A E).mapIso
      (BimoduleTensor.rightUnitIso A E D (BimoduleCategory.underlying A E D P) d) ≪≫
    (kernelDerivedColumnComputation A D E d P).symm

lemma perfectDerivedKernelAction_preserves (K : Kernel A D E) (hK : kernelColumnsPerfect A D E K)
    {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    modulePerfect A E ((kernelDerivedTensor A D E K).obj X) := by
  obtain ⟨⟨P⟩⟩ := K
  have hP := (kernelColumnsPerfect_ofBimodule_iff A D E P).1 hK
  exact (modulePerfect A E).prop_of_iso
    ((kernelDerivedTensorOnBimoduleIso A D E P).app X).symm
    (perfectKernelAction_preserves A D E (BimoduleCategory.underlying A E D P) hP hX)

def perfectDerivedKernelAction (K : Kernel A D E) (hK : kernelColumnsPerfect A D E K) :
    PerfectModuleCategory A D ⥤ PerfectModuleCategory A E :=
  perfectFunctorRestriction A D E (kernelDerivedTensor A D E K)
    (fun _ h => perfectDerivedKernelAction_preserves A D E K hK h)

lemma kernelColumnsPerfect_iff_preservesPerfect (K : Kernel A D E) :
    kernelColumnsPerfect A D E K ↔
      ∀ X, modulePerfect A D X → modulePerfect A E ((kernelDerivedTensor A D E K).obj X) := by
  constructor
  · intro hK X hX
    exact perfectDerivedKernelAction_preserves A D E K hK hX
  · intro h d
    exact (modulePerfect A E).prop_of_iso (kernelDerivedColumnActionIso A D E K d)
      (h _ (modulePerfectOver_representable A D d (Set.mem_univ _)))

def perfectDerivedKernelActionInclusionIso (K : Kernel A D E)
    (hK : kernelColumnsPerfect A D E K) :
    perfectDerivedKernelAction A D E K hK ⋙ perfectModuleInclusion A E Set.univ ≅
      perfectModuleInclusion A D Set.univ ⋙ kernelDerivedTensor A D E K := Iso.refl _

/-- kernelの任意の主導来射を、実際のPerf作用間の自然変換へ送る。 -/
def perfectDerivedKernelActionFunctor :
    (kernelColumnsPerfect A D E).FullSubcategory ⥤
      (PerfectModuleCategory A D ⥤ PerfectModuleCategory A E) where
  obj K := perfectDerivedKernelAction A D E K.obj K.property
  map {K L} f := perfectFunctorTransformation A D E _ _
    (fun _ h => perfectDerivedKernelAction_preserves A D E K.obj K.property h)
    (fun _ h => perfectDerivedKernelAction_preserves A D E L.obj L.property h)
    ((kernelDerivedTensorFunctor A D E).map f.hom)
  map_id K := by
    apply NatTrans.ext
    funext X
    apply (modulePerfect A E).hom_ext
    exact NatTrans.congr_app ((kernelDerivedTensorFunctor A D E).map_id K.obj) X.obj
  map_comp f g := by
    apply NatTrans.ext
    funext X
    apply (modulePerfect A E).hom_ext
    exact NatTrans.congr_app ((kernelDerivedTensorFunctor A D E).map_comp f.hom g.hom) X.obj

def perfectDerivedKernelMap {K L : Kernel A D E}
    (hK : kernelColumnsPerfect A D E K) (hL : kernelColumnsPerfect A D E L) (f : K ⟶ L) :
    perfectDerivedKernelAction A D E K hK ⟶ perfectDerivedKernelAction A D E L hL where
  app X := ObjectProperty.homMk (((kernelDerivedTensorFunctor A D E).map f).app X.obj)
  naturality _ _ g := (modulePerfect A E).hom_ext
    (((kernelDerivedTensorFunctor A D E).map f).naturality g.hom)

end SerrePositivity.DifferentialGraded.Morita
end

end PerfectKernelColumns

/-! ## PerfectKernelEvaluation（旧 SerrePositivity/DifferentialGraded/Morita/PerfectKernelEvaluation.lean） -/

/-! # 実際のkernel導来作用の評価とU12d導来tensorの自然比較

U14の評価比較と同じ既存のH⁰・主局所化計算を、任意kernelへ適用する。
-/

@[expose] public section PerfectKernelEvaluation
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

lemma perfectKernelTensor_map_π (M N : RightModule A D) (e : E) :
    (kernelTensor A D E P).map M N ≫
      moduleHomπ A E ((kernelTensor A D E P).obj M) ((kernelTensor A D E P).obj N) e =
        BalancedTensor.rightHomMap A D M N (P.leftAt e) := by
  have h := BimoduleTensor.compose_leftMap_π A E D (RightModule A D) P
    (DGFunctor.id (RightModule A D)) M N e
  exact h.trans (Category.id_comp _)

lemma perfectKernelTensor_map_eval {M N : ModuleCategory A D} (f : M ⟶ N) (e : E) :
    (moduleEvaluation A E e).map ((kernelTensor A D E P).onClosed.map f) =
      BalancedTensor.rightTensorMap A D (P.leftAt e) f := by
  apply Cochain.ofHom_injective
  rw [moduleEvaluation_cochain]
  change (moduleHomπ A E _ _ e).f 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f ≫
      (kernelTensor A D E P).map _ _)).val = _
  rw [cycleFromUnit_postcomp]
  have h := congrArg (fun k => k.f 0 (cycleFromUnit _
    (ForgetEnrichment.homTo (Complex A) f)).val)
      (perfectKernelTensor_map_π A D E P
        (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N) e)
  exact h.trans (BalancedTensor.rightHomMap_closedElement A D (P.leftAt e) f)

def perfectKernelTensorEvaluationIso (d : E) :
    (kernelTensor A D E P).onClosed ⋙ moduleEvaluation A E d ≅
      BalancedTensor.rightTensorFunctor A D
        (P.leftAt d) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    change (moduleEvaluation A E d).map ((kernelTensor A D E P).onClosed.map f) ≫ 𝟙 _ =
      𝟙 _ ≫ BalancedTensor.rightTensorMap A D
        (P.leftAt d) f
    rw [Category.comp_id, Category.id_comp]
    exact perfectKernelTensor_map_eval A D E P f d)

variable [HasDerivedCategory.{z} (ModuleCat.{u} A)]

/-- K(D)上のkernel作用評価を、閉零代表上でbalanced tensorと比較する。 -/
def perfectKernelTensorHomotopyEvaluationFacIso (d : E) :
    moduleToHomotopy A D ⋙
        (kernelTensor A D E P).onHomotopy ⋙
          moduleHomotopyToDerivedClosed A E ⋙ moduleDerivedEvaluation A E d ≅
      BalancedTensor.rightTensorFunctor A D
        (P.leftAt d) ⋙ DerivedCategory.Q :=
  (Functor.associator (moduleToHomotopy A D)
    (kernelTensor A D E P).onHomotopy
    (moduleHomotopyToDerivedClosed A E ⋙ moduleDerivedEvaluation A E d)).symm ≪≫
  Functor.isoWhiskerRight (eqToIso (kernelTensor A D E P).onHomotopy_fac)
    (moduleHomotopyToDerivedClosed A E ⋙ moduleDerivedEvaluation A E d) ≪≫
  Functor.associator (kernelTensor A D E P).onClosed (moduleToHomotopy A E)
    (moduleHomotopyToDerivedClosed A E ⋙ moduleDerivedEvaluation A E d) ≪≫
  Functor.isoWhiskerLeft (kernelTensor A D E P).onClosed
    ((Functor.associator (moduleToHomotopy A E) (moduleHomotopyToDerivedClosed A E)
      (moduleDerivedEvaluation A E d)).symm ≪≫ moduleDerivedEvaluationHomotopyFacIso A E d) ≪≫
  (Functor.associator (kernelTensor A D E P).onClosed (moduleEvaluation A E d)
    DerivedCategory.Q).symm ≪≫
  Functor.isoWhiskerRight (perfectKernelTensorEvaluationIso A D E P d) DerivedCategory.Q

/-- U12dのhomotopy tensorを、閉零代表上で同じbalanced tensorへ比較する。 -/
def perfectKernelU12dHomotopyTensorFacIso (d : E) :
    moduleToHomotopy A D ⋙
        BalancedTensor.rightTensorHomotopyFunctor A D
          (P.leftAt d) ⋙ DerivedCategory.Qh ≅
      BalancedTensor.rightTensorFunctor A D
        (P.leftAt d) ⋙ DerivedCategory.Q :=
  (Functor.associator (moduleToHomotopy A D)
    (BalancedTensor.rightTensorHomotopyFunctor A D
      (P.leftAt d)) DerivedCategory.Qh).symm ≪≫
  Functor.isoWhiskerRight
    (eqToIso (BalancedTensor.rightTensorHomotopyFunctor_fac A D
      (P.leftAt d))) DerivedCategory.Qh ≪≫
  Functor.associator
    (BalancedTensor.rightTensorFunctor A D
      (P.leftAt d))
    (_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)) DerivedCategory.Qh ≪≫
  Functor.isoWhiskerLeft
    (BalancedTensor.rightTensorFunctor A D
      (P.leftAt d))
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A))

/-- 全てのK(D)射に自然な、kernel作用評価とU12dの比較。 -/
def perfectKernelTensorHomotopyEvaluationIso (d : E) :
    (kernelTensor A D E P).onHomotopy ⋙
        moduleHomotopyToDerivedClosed A E ⋙ moduleDerivedEvaluation A E d ≅
      BalancedTensor.rightTensorHomotopyFunctor A D
        (P.leftAt d) ⋙ DerivedCategory.Qh :=
  Quotient.natIsoLift (boundaryRelation A (RightModule A D))
    (perfectKernelTensorHomotopyEvaluationFacIso A D E P d ≪≫
      (perfectKernelU12dHomotopyTensorFacIso A D E P d).symm)

/-- 任意の右射影解像度族について、導来tensorのE評価はU12dの導来tensorと自然同型。 -/
def perfectKernelResolutionDerivedTensorEvaluationIso
    (R : ∀ N : ModuleCategory A D,
      ModuleProjectiveResolution A D N) (d : E) :
    kernelResolutionDerivedTensor A D E P R ⋙ moduleDerivedEvaluation A E d ≅
      moduleResolutionDerivedTensor A D R
        (P.leftAt d) :=
  Functor.associator (moduleDerivedResolutionFunctor A D R)
    ((kernelTensor A D E P).onHomotopy ⋙ moduleHomotopyToDerivedClosed A E)
    (moduleDerivedEvaluation A E d) ≪≫
  Functor.isoWhiskerLeft (moduleDerivedResolutionFunctor A D R)
    (Functor.associator (kernelTensor A D E P).onHomotopy
      (moduleHomotopyToDerivedClosed A E) (moduleDerivedEvaluation A E d) ≪≫
        perfectKernelTensorHomotopyEvaluationIso A D E P d)

/-- 主kernel導来作用と既存U12d導来tensorの自然な評価正方形。 -/
def perfectKernelDerivedTensorEvaluationIso (d : E) :
    kernelDerivedTensorOnBimodule A D E P ⋙ moduleDerivedEvaluation A E d ≅
      moduleDerivedTensorRight A D
        (P.leftAt d) :=
  perfectKernelResolutionDerivedTensorEvaluationIso A D E P
    (moduleCanonicalProjectiveResolution A D) d
def perfectKernelActionEvaluationIso
    (hP : ∀ x : D, modulePerfect A E ((moduleToDerived A E).obj
      (ForgetEnrichment.of (Complex A) (P.rightAt x)))) (e : E) :
    perfectKernelAction A D E P hP ⋙ perfectModuleInclusion A E Set.univ ⋙
        moduleDerivedEvaluation A E e ≅
      perfectModuleInclusion A D Set.univ ⋙ moduleDerivedTensorRight A D (P.leftAt e) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (perfectKernelActionInclusionIso A D E P hP) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (perfectKernelDerivedTensorEvaluationIso A D E P e)

end SerrePositivity.DifferentialGraded.Morita
end

end PerfectKernelEvaluation

/-! ## PerfectKernelEvaluationNaturality（旧 SerrePositivity/DifferentialGraded/Morita/PerfectKernelEvaluationNaturality.lean） -/

/-! # kernel作用評価とU12d導来tensorの比較のkernel射自然性 -/

@[expose] public section PerfectKernelEvaluationNaturality
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  [HasDerivedCategory.{z} (ModuleCat.{u} A)]

lemma kernelHomotopyEvaluationIso_app (P : Bimodule A E D) (e : E)
    (M : ModuleCategory A D) :
    (perfectKernelTensorHomotopyEvaluationIso A D E P e).hom.app
        ((moduleToHomotopy A D).obj M) =
      (moduleDerivedEvaluationHomotopyFacIso A E e).hom.app
          ((kernelTensor A D E P).onClosed.obj M) ≫
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).inv.app
          ((BalancedTensor.rightTensorFunctor A D (P.leftAt e)).obj M) := by
  simp only [perfectKernelTensorHomotopyEvaluationIso, Quotient.natIsoLift_hom,
    Quotient.natTransLift_app, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    perfectKernelTensorHomotopyEvaluationFacIso, perfectKernelU12dHomotopyTensorFacIso,
    Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    eqToIso.hom, eqToIso.inv, eqToHom_app, perfectKernelTensorEvaluationIso,
    NatIso.ofComponents, Iso.refl_hom]
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  erw [Category.comp_id, Category.comp_id, Category.comp_id]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]

lemma kernelHomotopyEvaluationIso_naturality
    {P P' : BimoduleCategory A E D} (f : P ⟶ P') (e : E) :
    Functor.whiskerRight
        (Functor.whiskerRight (kernelTensorHomotopyMap A D E f)
          (moduleHomotopyToDerivedClosed A E)) (moduleDerivedEvaluation A E e) ≫
        (perfectKernelTensorHomotopyEvaluationIso A D E
          (BimoduleCategory.underlying A E D P') e).hom =
      (perfectKernelTensorHomotopyEvaluationIso A D E
        (BimoduleCategory.underlying A E D P) e).hom ≫
        Functor.whiskerRight (BalancedTensor.rightTensorHomotopyLeftMap A D
          ((BimoduleCategory.leftEvaluation A E D e).map f)) DerivedCategory.Qh := by
  apply NatTrans.ext
  funext X
  obtain ⟨M⟩ := X
  change (moduleDerivedEvaluation A E e).map ((moduleHomotopyToDerivedClosed A E).map
      ((kernelTensorHomotopyMap A D E f).app ((moduleToHomotopy A D).obj M))) ≫
      (perfectKernelTensorHomotopyEvaluationIso A D E
        (BimoduleCategory.underlying A E D P') e).hom.app ((moduleToHomotopy A D).obj M) =
    (perfectKernelTensorHomotopyEvaluationIso A D E
      (BimoduleCategory.underlying A E D P) e).hom.app ((moduleToHomotopy A D).obj M) ≫
      DerivedCategory.Qh.map ((BalancedTensor.rightTensorHomotopyLeftMap A D
        ((BimoduleCategory.leftEvaluation A E D e).map f)).app ((moduleToHomotopy A D).obj M))
  rw [kernelTensorHomotopyMap_app, kernelHomotopyEvaluationIso_app,
    kernelHomotopyEvaluationIso_app, BalancedTensor.rightTensorHomotopyLeftMap_app]
  have h := (moduleDerivedEvaluationHomotopyFacIso A E e).hom.naturality
    ((kernelTensorMap A D E f).app M)
  simp only [Functor.comp_map] at h
  rw [← Category.assoc]
  erw [h]
  rw [Category.assoc]
  dsimp only [moduleEvaluationToDerived, Functor.comp_map]
  erw [kernelTensorMap_value, DerivedCategory.quotientCompQhIso_inv_naturality]
  exact (Category.assoc _ _ _).symm

lemma kernelResolutionEvaluationIso_naturality
    (R : ∀ M : ModuleCategory A D, ModuleProjectiveResolution A D M)
    {P P' : BimoduleCategory A E D} (f : P ⟶ P') (e : E) :
    Functor.whiskerRight (kernelResolutionDerivedTensorMap A D E R f)
        (moduleDerivedEvaluation A E e) ≫
        (perfectKernelResolutionDerivedTensorEvaluationIso A D E
          (BimoduleCategory.underlying A E D P') R e).hom =
      (perfectKernelResolutionDerivedTensorEvaluationIso A D E
        (BimoduleCategory.underlying A E D P) R e).hom ≫
        (moduleResolutionDerivedTensorLeftFunctor A D R).map
          ((BimoduleCategory.leftEvaluation A E D e).map f) := by
  apply NatTrans.ext
  funext X
  have h := NatTrans.congr_app (kernelHomotopyEvaluationIso_naturality A D E f e)
    ((moduleDerivedResolutionFunctor A D R).obj X)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    perfectKernelResolutionDerivedTensorEvaluationIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.associator_hom_app]
  erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp]
  exact h

lemma kernelDerivedEvaluationIso_naturality
    {P P' : BimoduleCategory A E D} (f : P ⟶ P') (e : E) :
    Functor.whiskerRight ((kernelDerivedTensorOnBimoduleFunctor A D E).map f)
        (moduleDerivedEvaluation A E e) ≫
        (perfectKernelDerivedTensorEvaluationIso A D E
          (BimoduleCategory.underlying A E D P') e).hom =
      (perfectKernelDerivedTensorEvaluationIso A D E
        (BimoduleCategory.underlying A E D P) e).hom ≫
        (moduleDerivedTensorLeftFunctor A D).map
          ((BimoduleCategory.leftEvaluation A E D e).map f) :=
  kernelResolutionEvaluationIso_naturality A D E (moduleCanonicalProjectiveResolution A D) f e

/-- 実際のkernel作用の評価を、kernel変数に関する関手として読む。 -/
def kernelDerivedEvaluationFunctor (e : E) :
    BimoduleCategory A E D ⥤
      (DerivedModuleCategory A D ⥤ DerivedCategory (ModuleCat.{u} A)) :=
  kernelDerivedTensorOnBimoduleFunctor A D E ⋙
    (Functor.whiskeringRight (DerivedModuleCategory A D) (DerivedModuleCategory A E)
      (DerivedCategory (ModuleCat.{u} A))).obj (moduleDerivedEvaluation A E e)

/-- 既存評価比較はkernel変数と導来入力の両方に自然な関手自然同型。 -/
def kernelDerivedEvaluationIso (e : E) :
    kernelDerivedEvaluationFunctor A D E e ≅
      BimoduleCategory.leftEvaluation A E D e ⋙ moduleDerivedTensorLeftFunctor A D :=
  NatIso.ofComponents
    (fun P => perfectKernelDerivedTensorEvaluationIso A D E
      (BimoduleCategory.underlying A E D P) e)
    (by intro P P' f; exact kernelDerivedEvaluationIso_naturality A D E f e)

end SerrePositivity.DifferentialGraded.Morita
end

end PerfectKernelEvaluationNaturality

/-! ## PerfectKernelComposition（旧 SerrePositivity/DifferentialGraded/Morita/PerfectKernelComposition.lean） -/

/-! # U16d：主導来kernel合成比較の主Perfへの制限

U16aの主導来作用族と合成自然同型を明示した入力として使う。
実際の通常kernelのPerf作用とkernelComposeの正しい向き・局所Hom条件を保持する。
-/

@[expose] public section PerfectKernelComposition
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (B : Type z) [DGCategory A B] [Small.{u} B]
  (P : Bimodule A E D) (Q : Bimodule A B E)
  (hP : ∀ d : D, modulePerfect A E ((moduleToDerived A E).obj
    (ForgetEnrichment.of (Complex A) (P.rightAt d))))
  (hQ : ∀ e : E, modulePerfect A B ((moduleToDerived A B).obj
    (ForgetEnrichment.of (Complex A) (Q.rightAt e))))
  (hD : localHomKFlat A D)
  (Action : Kernel A D B ⥤ (DerivedModuleCategory A D ⥤ DerivedModuleCategory A B))

def perfectKernelCompositeTarget : DerivedModuleCategory A D ⥤ DerivedModuleCategory A B :=
  Action.obj (kernelCompose A D E B hD
    ((bimoduleToDerived A E D).obj (BimoduleCategory.of A E D P))
    ((bimoduleToDerived A B E).obj (BimoduleCategory.of A B E Q)))

variable (eComp : kernelDerivedTensorOnBimodule A D E P ⋙
  kernelDerivedTensorOnBimodule A E B Q ≅ perfectKernelCompositeTarget A D E B P Q hD Action)
include hP hQ eComp

lemma perfectKernelComposite_preserves {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    modulePerfect A B ((perfectKernelCompositeTarget A D E B P Q hD Action).obj X) :=
  (modulePerfect A B).prop_of_iso (eComp.app X)
    (perfectKernelAction_preserves A E B Q hQ (perfectKernelAction_preserves A D E P hP hX))

def perfectKernelCompositeAction : PerfectModuleCategory A D ⥤ PerfectModuleCategory A B :=
  perfectFunctorRestriction A D B (perfectKernelCompositeTarget A D E B P Q hD Action)
    (fun _ h => perfectKernelComposite_preserves A D E B P Q hP hQ hD Action eComp h)

def perfectKernelCompositionComparisonIso :
    perfectKernelAction A D E P hP ⋙ perfectKernelAction A E B Q hQ ≅
      perfectKernelCompositeAction A D E B P Q hP hQ hD Action eComp :=
  perfectFunctorCompositionIso A D E B
      (kernelDerivedTensorOnBimodule A D E P) (kernelDerivedTensorOnBimodule A E B Q)
      (fun _ h => perfectKernelAction_preserves A D E P hP h)
      (fun _ h => perfectKernelAction_preserves A E B Q hQ h) ≪≫
    perfectFunctorIso A D B _ _
      (fun _ h => perfectKernelAction_preserves A E B Q hQ
        (perfectKernelAction_preserves A D E P hP h))
      (fun _ h => perfectKernelComposite_preserves A D E B P Q hP hQ hD Action eComp h) eComp

lemma perfectKernelCompositionComparisonIso_inclusion :
    Functor.whiskerRight
        (perfectKernelCompositionComparisonIso A D E B P Q hP hQ hD Action eComp).hom
        (perfectModuleInclusion A B Set.univ) =
      Functor.whiskerLeft (perfectModuleInclusion A D Set.univ) eComp.hom := by
  apply NatTrans.ext
  funext X
  change 𝟙 _ ≫ eComp.hom.app X.obj = eComp.hom.app X.obj
  exact Category.id_comp _

end SerrePositivity.DifferentialGraded.Morita
end

end PerfectKernelComposition

/-! ## PerfectProjectiveImage（旧 SerrePositivity/DifferentialGraded/Morita/PerfectProjectiveImage.lean） -/

/-!
概要：代表加群の perfect-projective 像から、全 perfect-projective 加群の像を制御する。
方針：有限 cell の像の射影性を帰納で示し、導来 retract をホモトピー retract に戻す。
規約：任意の全次数 dg 関手を用い、左随伴性・全準同型保存・模型の小ささを追加しない。
使われ方：K-S• の実 perfect 値 tensor 評価の制限。
-/

@[expose] public noncomputable section PerfectProjectiveImage
universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (E : Type w) [DGCategory R E] [Small.{u} E]

/-- 代表加群の射影的な像から、有限 cell の像の全 Hom 射影性を得る。 -/
lemma perfectDGFunctorImage_projective_finiteCell
    (T : DGFunctor R (RightModule R D) (RightModule R E))
    (hgen : ∀ d : D, moduleHomotopicallyProjective R E
      (ForgetEnrichment.of (Complex R) (T.obj (representable R d))))
    {M : ModuleCategory R D} (hM : moduleFiniteCell R D M) :
    moduleHomotopicallyProjective R E (T.onClosed.obj M) := by
  let F := T.onClosed
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  obtain ⟨c⟩ := hM
  induction c with
  | zero =>
      exact moduleHomotopicallyProjective_of_isZero R E
        (F.map_isZero (moduleZero_isZero R D))
  | generator d _ => exact hgen d
  | @shift M s c ih =>
      exact moduleHomotopicallyProjective_of_iso R E
        (dgModuleFunctorShiftIso R E D T s (ForgetEnrichment.to (Complex R) M)).symm
        (moduleHomotopicallyProjective_shift R E ih s)
  | @sum M N c d ihc ihd =>
      let e := F.mapIso (moduleBiprodIso R D M N) ≪≫ F.mapBiprod M N ≪≫
        (moduleBiprodIso R E (F.obj M) (F.obj N)).symm
      exact moduleHomotopicallyProjective_of_iso R E e.symm
        (moduleHomotopicallyProjective_biprod R E ihc ihd)
  | @cone M N c d f ihc ihd =>
      exact moduleHomotopicallyProjective_of_iso R E (dgModuleFunctorConeIso R D E T f)
        (moduleHomotopicallyProjective_cone R E ihc ihd (F.map f))
  | iso c e ih => exact moduleHomotopicallyProjective_of_iso R E (F.mapIso e) ih

/-- 射影的 perfect 源の導来 retract を実ホモトピー retract へ持ち上げて像を評価する。 -/
lemma perfectDGFunctorImage_projective
    (T : DGFunctor R (RightModule R D) (RightModule R E))
    (hgen : ∀ d : D, moduleHomotopicallyProjective R E
      (ForgetEnrichment.of (Complex R) (T.obj (representable R d))))
    {M : ModuleCategory R D} (hM : moduleHomotopicallyProjective R D M)
    (hPerf : modulePerfect R D ((moduleToDerived R D).obj M)) :
    moduleHomotopicallyProjective R E (T.onClosed.obj M) := by
  let F := T.onClosed
  let Q := moduleToHomotopy R D
  obtain ⟨N, hN, ⟨a⟩⟩ := (modulePerfect_iff R D _).1 hPerf
  have hNP := moduleFiniteCellOver_homotopicallyProjective R D hN
  obtain ⟨i, hi⟩ := moduleProjectiveToDerived_map_surjective R D hM a.i
  obtain ⟨r, hr⟩ := moduleProjectiveToDerived_map_surjective R D hNP a.r
  have h : Q.map (i ≫ r) = Q.map (𝟙 M) := by
    apply (moduleProjectiveDerivedHomEquiv R D hM M).injective
    rw [moduleProjectiveDerivedHomEquiv_map, moduleProjectiveDerivedHomEquiv_map,
      CategoryTheory.Functor.map_comp, hi, hr, a.retract, CategoryTheory.Functor.map_id]
  apply moduleHomotopicallyProjective_of_homotopyRetract R E (F.map i) (F.map r) _
    (perfectDGFunctorImage_projective_finiteCell R D E T hgen hN)
  have he := congrArg T.onHomotopy.map h
  change (moduleToHomotopy R E).map (F.map (i ≫ r)) =
    (moduleToHomotopy R E).map (F.map (𝟙 M)) at he
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using he

/-- 任意の dg 関手は、代表加群の perfect-projective 像から全 perfect-projective 像を得る。 -/
lemma perfectDGFunctorImage_perfectProjective
    (T : DGFunctor R (RightModule R D) (RightModule R E))
    (hgen : ∀ d : D, modulePerfectProjectiveOver R E Set.univ
      (T.obj (representable R d)))
    {M : RightModule R D} (hM : modulePerfectProjectiveOver R D Set.univ M) :
    modulePerfectProjectiveOver R E Set.univ (T.obj M) :=
  ⟨perfectDGFunctorImage_projective R D E T (fun d => (hgen d).1) hM.1 hM.2,
    perfectDGFunctorImage_projectivePerfect R D E T (fun d => (hgen d).2) hM.1 hM.2⟩

end SerrePositivity.DifferentialGraded.Morita

end PerfectProjectiveImage

/-! ## PerfectDerivedKernelCoherence（旧 SerrePositivity/DifferentialGraded/Morita/PerfectDerivedKernelCoherence.lean） -/

/-! # 実際の主導来kernelの恒等作用と、明示した合成比較のPerf制限

恒等比較はU16aの公開済みの実際の自然同型を使用する。
合成比較はU16aの型どおりの自然同型を明示して受け取り、局所Hom条件を保持する。
-/

@[expose] public section PerfectDerivedKernelCoherence
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma kernelIdentity_columnsPerfect : kernelColumnsPerfect A D D (kernelIdentity A D) := by
  apply (kernelColumnsPerfect_iff_preservesPerfect A D D _).2
  intro X hX
  exact (modulePerfect A D).prop_of_iso ((kernelIdentityIso A D).app X).symm hX

def perfectDerivedKernelIdentityIso :
    perfectDerivedKernelAction A D D (kernelIdentity A D) (kernelIdentity_columnsPerfect A D) ≅
      𝟭 (PerfectModuleCategory A D) :=
  perfectFunctorIso A D D _ _
      (fun _ h => perfectDerivedKernelAction_preserves A D D _
        (kernelIdentity_columnsPerfect A D) h) (fun _ h => h) (kernelIdentityIso A D) ≪≫
    perfectFunctorIdentityIso A D

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (B : Type z) [DGCategory A B] [Small.{u} B]
  (hD : localHomKFlat A D) (P : Kernel A D E) (Q : Kernel A E B)
  (hP : kernelColumnsPerfect A D E P) (hQ : kernelColumnsPerfect A E B Q)
  (eComp : kernelDerivedTensor A D E P ⋙ kernelDerivedTensor A E B Q ≅
    kernelDerivedTensor A D B (kernelCompose A D E B hD P Q))
include hP hQ eComp

lemma kernelCompose_columnsPerfect :
    kernelColumnsPerfect A D B (kernelCompose A D E B hD P Q) := by
  apply (kernelColumnsPerfect_iff_preservesPerfect A D B _).2
  intro X hX
  exact (modulePerfect A B).prop_of_iso (eComp.app X)
    (perfectDerivedKernelAction_preserves A E B Q hQ
      (perfectDerivedKernelAction_preserves A D E P hP hX))

def perfectDerivedKernelCompositionIso :
    perfectDerivedKernelAction A D E P hP ⋙ perfectDerivedKernelAction A E B Q hQ ≅
      perfectDerivedKernelAction A D B (kernelCompose A D E B hD P Q)
        (kernelCompose_columnsPerfect A D E B hD P Q hP hQ eComp) :=
  perfectFunctorCompositionIso A D E B _ _
      (fun _ h => perfectDerivedKernelAction_preserves A D E P hP h)
      (fun _ h => perfectDerivedKernelAction_preserves A E B Q hQ h) ≪≫
    perfectFunctorIso A D B _ _
      (fun _ h => perfectDerivedKernelAction_preserves A E B Q hQ
        (perfectDerivedKernelAction_preserves A D E P hP h))
      (fun _ h => perfectDerivedKernelAction_preserves A D B _
        (kernelCompose_columnsPerfect A D E B hD P Q hP hQ eComp) h) eComp

lemma perfectDerivedKernelCompositionIso_inclusion :
    Functor.whiskerRight
        (perfectDerivedKernelCompositionIso A D E B hD P Q hP hQ eComp).hom
        (perfectModuleInclusion A B Set.univ) =
      Functor.whiskerLeft (perfectModuleInclusion A D Set.univ) eComp.hom := by
  apply NatTrans.ext
  funext X
  change 𝟙 _ ≫ eComp.hom.app X.obj = eComp.hom.app X.obj
  exact Category.id_comp _

lemma perfectDerivedKernelCompositionIso_naturality
    (P' : Kernel A D E) (Q' : Kernel A E B)
    (hP' : kernelColumnsPerfect A D E P') (hQ' : kernelColumnsPerfect A E B Q')
    (eComp' : kernelDerivedTensor A D E P' ⋙ kernelDerivedTensor A E B Q' ≅
      kernelDerivedTensor A D B (kernelCompose A D E B hD P' Q'))
    (f : P ⟶ P') (g : Q ⟶ Q')
    (hNat : NatTrans.hcomp ((kernelDerivedTensorFunctor A D E).map f)
        ((kernelDerivedTensorFunctor A E B).map g) ≫ eComp'.hom =
      eComp.hom ≫ (kernelDerivedTensorFunctor A D B).map
        (kernelComposeMap A D E B hD f g)) :
    NatTrans.hcomp (perfectDerivedKernelMap A D E hP hP' f)
        (perfectDerivedKernelMap A E B hQ hQ' g) ≫
        (perfectDerivedKernelCompositionIso A D E B hD P' Q' hP' hQ' eComp').hom =
      (perfectDerivedKernelCompositionIso A D E B hD P Q hP hQ eComp).hom ≫
        perfectDerivedKernelMap A D B
          (kernelCompose_columnsPerfect A D E B hD P Q hP hQ eComp)
          (kernelCompose_columnsPerfect A D E B hD P' Q' hP' hQ' eComp')
          (kernelComposeMap A D E B hD f g) := by
  apply NatTrans.ext
  funext X
  apply (modulePerfect A B).hom_ext
  have h := NatTrans.congr_app hNat X.obj
  simp only [NatTrans.comp_app, NatTrans.hcomp_app] at h
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, perfectDerivedKernelCompositionIso,
    perfectFunctorCompositionIso, perfectFunctorIso, Iso.trans_hom, NatIso.ofComponents,
    ObjectProperty.isoMk, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app]
  change
    ((((kernelDerivedTensorFunctor A E B).map g).app
        ((kernelDerivedTensor A D E P).obj X.obj) ≫
      (kernelDerivedTensor A E B Q').map
        (((kernelDerivedTensorFunctor A D E).map f).app X.obj)) ≫
      𝟙 _ ≫ eComp'.hom.app X.obj) =
    (𝟙 _ ≫ eComp.hom.app X.obj) ≫
      ((kernelDerivedTensorFunctor A D B).map (kernelComposeMap A D E B hD f g)).app X.obj
  simpa only [Category.id_comp, kernelDerivedTensor, Functor.comp_obj] using h

end SerrePositivity.DifferentialGraded.Morita
end

end PerfectDerivedKernelCoherence

/-! ## PerfectDerivedKernelComposition（旧 SerrePositivity/DifferentialGraded/Morita/PerfectDerivedKernelComposition.lean） -/

/-! # 公開された実際の主導来kernel合成比較のPerf制限

合成同型そのものは追加の入力を要求せず、U16aのkernelCompositionIsoを使用する。
kernel射の自然性はU16aの未完項目なので、対応する図式を明示して受け取る。
-/

@[expose] public section PerfectDerivedKernelComposition
universe u v w z

noncomputable section
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (B : Type z) [DGCategory A B] [Small.{u} B]
  (hD : localHomKFlat A D) (P : Kernel A D E) (Q : Kernel A E B)
  (hP : kernelColumnsPerfect A D E P) (hQ : kernelColumnsPerfect A E B Q)
include hP hQ

lemma kernelCompose_columnsPerfect_of_columns :
    kernelColumnsPerfect A D B (kernelCompose A D E B hD P Q) :=
  kernelCompose_columnsPerfect A D E B hD P Q hP hQ (kernelCompositionIso A D E B hD P Q)

def perfectKernelCompositionIso :
    perfectDerivedKernelAction A D E P hP ⋙ perfectDerivedKernelAction A E B Q hQ ≅
      perfectDerivedKernelAction A D B (kernelCompose A D E B hD P Q)
        (kernelCompose_columnsPerfect_of_columns A D E B hD P Q hP hQ) :=
  perfectDerivedKernelCompositionIso A D E B hD P Q hP hQ
    (kernelCompositionIso A D E B hD P Q)

lemma perfectKernelCompositionIso_inclusion :
    Functor.whiskerRight (perfectKernelCompositionIso A D E B hD P Q hP hQ).hom
        (perfectModuleInclusion A B Set.univ) =
      Functor.whiskerLeft (perfectModuleInclusion A D Set.univ)
        (kernelCompositionIso A D E B hD P Q).hom :=
  perfectDerivedKernelCompositionIso_inclusion A D E B hD P Q hP hQ
    (kernelCompositionIso A D E B hD P Q)

lemma perfectKernelCompositionIso_naturality
    (P' : Kernel A D E) (Q' : Kernel A E B)
    (hP' : kernelColumnsPerfect A D E P') (hQ' : kernelColumnsPerfect A E B Q')
    (f : P ⟶ P') (g : Q ⟶ Q')
    (hNat : NatTrans.hcomp ((kernelDerivedTensorFunctor A D E).map f)
        ((kernelDerivedTensorFunctor A E B).map g) ≫
        (kernelCompositionIso A D E B hD P' Q').hom =
      (kernelCompositionIso A D E B hD P Q).hom ≫
        (kernelDerivedTensorFunctor A D B).map (kernelComposeMap A D E B hD f g)) :
    NatTrans.hcomp (perfectDerivedKernelMap A D E hP hP' f)
        (perfectDerivedKernelMap A E B hQ hQ' g) ≫
        (perfectKernelCompositionIso A D E B hD P' Q' hP' hQ').hom =
      (perfectKernelCompositionIso A D E B hD P Q hP hQ).hom ≫
        perfectDerivedKernelMap A D B
          (kernelCompose_columnsPerfect_of_columns A D E B hD P Q hP hQ)
          (kernelCompose_columnsPerfect_of_columns A D E B hD P' Q' hP' hQ')
          (kernelComposeMap A D E B hD f g) :=
  perfectDerivedKernelCompositionIso_naturality A D E B hD P Q hP hQ
    (kernelCompositionIso A D E B hD P Q) P' Q' hP' hQ'
    (kernelCompositionIso A D E B hD P' Q') f g hNat

/-- 実際の合成比較は、両kernelの任意の主導来射に対してPerf上でも自然。 -/
lemma perfectKernelCompositionIso_kernel_naturality
    (P' : Kernel A D E) (Q' : Kernel A E B)
    (hP' : kernelColumnsPerfect A D E P') (hQ' : kernelColumnsPerfect A E B Q')
    (f : P ⟶ P') (g : Q ⟶ Q') :
    NatTrans.hcomp (perfectDerivedKernelMap A D E hP hP' f)
        (perfectDerivedKernelMap A E B hQ hQ' g) ≫
        (perfectKernelCompositionIso A D E B hD P' Q' hP' hQ').hom =
      (perfectKernelCompositionIso A D E B hD P Q hP hQ).hom ≫
        perfectDerivedKernelMap A D B
          (kernelCompose_columnsPerfect_of_columns A D E B hD P Q hP hQ)
          (kernelCompose_columnsPerfect_of_columns A D E B hD P' Q' hP' hQ')
          (kernelComposeMap A D E B hD f g) :=
  perfectKernelCompositionIso_naturality A D E B hD P Q hP hQ P' Q' hP' hQ' f g
    (kernelCompositionIso_naturality A D E B hD f g)

end SerrePositivity.DifferentialGraded.Morita
end

end PerfectDerivedKernelComposition
