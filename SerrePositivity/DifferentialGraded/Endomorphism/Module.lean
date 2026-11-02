module

public import SerrePositivity.DifferentialGraded.Endomorphism.Basic
public import SerrePositivity.DifferentialGraded.Bimodule.Basic
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement
public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements
public import SerrePositivity.DifferentialGraded.Tensor.Enriched

public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
public import SerrePositivity.DifferentialGraded.Tensor.Fubini
public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Endomorphism.Module

## 概要
10 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## HomBimodule（旧 SerrePositivity/DifferentialGraded/Endomorphism/HomBimodule.lean） -/

/-! # 指定対象からのHomを値とするendomorphism bimodule -/

@[expose] public section HomBimodule
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D] (E : D)

/-- Hom(E,X)の右End(E)作用は、代表加群の指定対象への制限である。 -/
def endomorphismHomRight (X : D) : RightModule A (EndomorphismObject E) :=
  restrictModule A _ D (endomorphismInclusion A E).op (representable A X)

/-- Yonedaの全次数自然族を一対象上に制限する。 -/
def endomorphismHomParam (X Y : D) :
    ModuleParamTrans A (EndomorphismObject E) (X ⟶[Complex A] Y)
      (endomorphismHomRight A D E X) (endomorphismHomRight A D E Y) where
  app _ := ((Bimodule.diagonal A D).paramTrans X Y).app (op E)
  naturality x y := by
    change (β_ (X ⟶[Complex A] Y) (op E ⟶[Complex A] op E)).hom ≫
      ((𝟙 _ ≫ (representable A X).map (op E) (op E)) ⊗ₘ
        ((Bimodule.diagonal A D).paramTrans X Y).app (op E)) ≫ enrichedComposition _ _ _ =
      (((Bimodule.diagonal A D).paramTrans X Y).app (op E) ⊗ₘ
        (𝟙 _ ≫ (representable A Y).map (op E) (op E))) ≫ enrichedComposition _ _ _
    simp only [Category.id_comp]
    exact ((Bimodule.diagonal A D).paramTrans X Y).naturality (op E) (op E)

/-- 右End(E)・左Dのbimodule。全次数Hom endに値を持つ。 -/
def endomorphismHomBimodule : Bimodule A (EndomorphismObject E) D :=
  Bimodule.ofParamTrans A _ D (endomorphismHomRight A D E)
    (endomorphismHomParam A D E)
    (fun X _ => (Bimodule.diagonal A D).paramTrans_unit X (op E))
    (fun X Y Z _ => (Bimodule.diagonal A D).paramTrans_comp X Y Z (op E))

/-- bimoduleの値は指定対象からの全Hom複体。 -/
lemma endomorphismHomBimodule_value (b : EndomorphismObject E) (X : D) :
    (endomorphismHomBimodule A D E).value b X = homObject A D E X := rfl

/-- 既存Yonedaとの比較：各右加群はYoneda像の制限そのもの。 -/
lemma endomorphismHomBimodule_rightAt (X : D) :
    (endomorphismHomBimodule A D E).rightAt X =
      restrictModule A _ D (endomorphismInclusion A E).op ((dgYoneda A D).obj X) := rfl

/-- 左D作用の成分は既存dg YonedaのHom写像のE成分。 -/
lemma endomorphismHomBimodule_map_π (X Y : D) (b : EndomorphismObject E) :
    (endomorphismHomBimodule A D E).map X Y ≫
      moduleHomπ A _ (endomorphismHomRight A D E X) (endomorphismHomRight A D E Y) b =
    yonedaHom A D X Y ≫ moduleHomπ A D (representable A X) (representable A Y) E :=
  Bimodule.ofParamTrans_map_π A _ D _ _ _ _ X Y b

omit [Small.{u} D] in
/-- E自身の像はEnd(E)の正則右加群。全次数の作用も一致する。 -/
lemma endomorphismHomRight_self :
    endomorphismHomRight A D E E = representable A (EndomorphismObject.point (E := E)) := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]

/-- U13の小さいenhancement内の指定対象に対するEnd表示bimodule。 -/
abbrev perfectEndomorphismHomBimodule (S : Set D) (E : SmallPerfectDGModuleOver A D S) :=
  endomorphismHomBimodule A (SmallPerfectDGModuleOver A D S) E

end SerrePositivity.DifferentialGraded
end

end HomBimodule

/-! ## Evaluation（旧 SerrePositivity/DifferentialGraded/Endomorphism/Evaluation.lean） -/

/-! # End(E)上のbalanced合成評価

Hom(E,Y) ⊗_End(E) Hom(X,E) → Hom(X,Y)を構成する。
tensorの入力順を交換するKoszul符号を明示する。
-/

@[expose] public section Evaluation
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (E : D)

/-- Hom(X,E)の左End(E)作用。 -/
def endomorphismHomLeft (X : D) : LeftModule A (EndomorphismObject E) :=
  (endomorphismInclusion A E).comp (leftRepresentable A X)

/-- balanced評価の余等化前のchain map。 -/
def endomorphismEvaluationComponent (X Y : D) :
    homObject A D E Y ⊗ homObject A D X E ⟶ homObject A D X Y :=
  (signedSwap _ _).hom ≫ eComp (Complex A) X E Y

lemma endomorphismEvaluationComponent_apply (X Y : D) {r s n : ℤ}
    (m : GradedHom A E Y r) (t : GradedHom A X E s) (hn : r + s = n) :
    (endomorphismEvaluationComponent A D E X Y).f n
      (ιTensorObj (homObject A D E Y) (homObject A D X E) r s n hn (m ⊗ₜ[A] t)) =
    (r * s).negOnePow • forward A t m (by omega) := by
  change (eComp (Complex A) X E Y).f n
    ((signedSwap _ _).hom.f n (ιTensorObj (homObject A D E Y) (homObject A D X E)
      r s n hn (m ⊗ₜ[A] t))) = _
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]
  rfl

/-- 合成の結合則はEnd(E)上のbalanced関係を満たす。 -/
def endomorphismEvaluationFamily (X Y : D) :
    BalancedTensor.BalancedFamily A (EndomorphismObject E)
      (endomorphismHomRight A D E Y) (endomorphismHomLeft A D E X) (homObject A D X Y) := by
  apply BalancedTensor.balancedFamilyMk A (EndomorphismObject E)
    (M := endomorphismHomRight A D E Y) (N := endomorphismHomLeft A D E X)
    (fun _ => endomorphismEvaluationComponent A D E X Y)
  intro x y r p s n hn m f t
  change GradedHom A E Y r at m
  change GradedHom A E E p at f
  change GradedHom A X E s at t
  change (r * p).negOnePow • (endomorphismEvaluationComponent A D E X Y).f n
    (ιTensorObj (homObject A D E Y) (homObject A D X E) (r + p) s n hn
      (moduleAction A (endomorphismHomRight A D E Y) (x := op y) (y := op x) f m rfl ⊗ₜ[A] t)) =
    (endomorphismEvaluationComponent A D E X Y).f n
      (ιTensorObj (homObject A D E Y) (homObject A D X E) r (p + s) n (by omega)
        (m ⊗ₜ[A] SerrePositivity.DifferentialGraded.leftAction A
          (endomorphismHomLeft A D E X) (x := x) (y := y) f t (by omega)))
  rw [endomorphismEvaluationComponent_apply, endomorphismEvaluationComponent_apply]
  have hr : moduleAction A (endomorphismHomRight A D E Y) (x := op y) (y := op x) f m rfl =
      forward A (D := D) (x := E) (y := E) (z := Y) f m (by omega) := rfl
  have hl : SerrePositivity.DifferentialGraded.leftAction A (endomorphismHomLeft A D E X)
      (x := x) (y := y) f t (by omega : s + p = p + s) =
      (p * s).negOnePow • forward A (D := D) (x := X) (y := E) (z := E) t f
        (by omega : s + p = p + s) := by
    exact leftRepresentable_action A X E E f t (by omega)
  rw [hr, hl]
  have hs := forward_assoc_of_sum A (D := D) (w := X) (x := E) (y := E) (z := Y)
    t f m (by omega : s + p = p + s)
    (by omega : p + r = r + p) (by omega : p + s + r = n)
  have hsmul : forward A (D := D) (x := X) (y := E) (z := Y)
      ((p * s).negOnePow • forward A t f (by omega : s + p = p + s)) m
      (by omega : p + s + r = n) =
      (p * s).negOnePow • forward A (forward A t f (by omega : s + p = p + s)) m
        (by omega : p + s + r = n) := by
    simp only [forward, Units.smul_def, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_zsmul]
  rw [hsmul, hs]
  simp only [smul_smul, ← Int.negOnePow_add]
  rw [show r * p + (r + p) * s = r * (p + s) + p * s by ring]

/-- 指定対象を通るbalanced合成評価。 -/
def endomorphismEvaluation (X Y : D) :
    BalancedTensor.obj A (EndomorphismObject E)
      (endomorphismHomRight A D E Y) (endomorphismHomLeft A D E X) ⟶ homObject A D X Y :=
  BalancedTensor.desc A _ _ _ (endomorphismEvaluationFamily A D E X Y)

@[reassoc (attr := simp)]
lemma endomorphismEvaluation_ι (X Y : D) (b : EndomorphismObject E) :
    BalancedTensor.ι A _ (endomorphismHomRight A D E Y) (endomorphismHomLeft A D E X) b ≫
      endomorphismEvaluation A D E X Y = endomorphismEvaluationComponent A D E X Y :=
  BalancedTensor.ι_desc A _ _ _ _ b

end SerrePositivity.DifferentialGraded
end

end Evaluation

/-! ## EvaluationAdjunction（旧 SerrePositivity/DifferentialGraded/Endomorphism/EvaluationAdjunction.lean） -/

/-! # balanced合成評価と既存tensor–Hom随伴の比較

ここではHom(X,E)を固定した複体値の随伴を使う。
enhancement全体とEnd(E)加群の間の再構成随伴とは区別する。
-/

@[expose] public section EvaluationAdjunction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (E : D)

/-- 評価のtensor–Hom転置は右End(E)加群の実際の閉零射である。 -/
def endomorphismEvaluationMate (X Y : D) :
    ForgetEnrichment.of (Complex A) (endomorphismHomRight A D E Y) ⟶
      ForgetEnrichment.of (Complex A)
        (homRightModule A (EndomorphismObject E)
          (endomorphismHomLeft A D E X) (homObject A D X Y)) :=
  BalancedTensor.tensorHomEquiv A _ _ _ _ (endomorphismEvaluation A D E X Y)

/-- 単位との比較：評価の転置は既存随伴の単位と右随伴による評価の像の合成。 -/
lemma endomorphismEvaluationMate_unit (X Y : D) :
    endomorphismEvaluationMate A D E X Y =
      (BalancedTensor.tensorHomAdjunction A _ (endomorphismHomLeft A D E X)).unit.app
          (ForgetEnrichment.of (Complex A) (endomorphismHomRight A D E Y)) ≫
        (homRightFunctor A _ (endomorphismHomLeft A D E X)).map
          (endomorphismEvaluation A D E X Y) := by
  change BalancedTensor.tensorHomEquiv A _ _ _ _ _ = _
  rw [← BalancedTensor.tensorHomAdjunction_homEquiv]
  exact (BalancedTensor.tensorHomAdjunction A _ (endomorphismHomLeft A D E X)).homEquiv_unit _ _ _

/-- 余単位との比較：balanced評価はその転置をtensorして余単位で評価したもの。 -/
lemma endomorphismEvaluation_counit (X Y : D) :
    endomorphismEvaluation A D E X Y =
      (BalancedTensor.rightTensorFunctor A _ (endomorphismHomLeft A D E X)).map
          (endomorphismEvaluationMate A D E X Y) ≫
        (BalancedTensor.tensorHomAdjunction A _ (endomorphismHomLeft A D E X)).counit.app
          (homObject A D X Y) := by
  have h := (BalancedTensor.tensorHomAdjunction A _ (endomorphismHomLeft A D E X)).homEquiv_counit
    (g := endomorphismEvaluationMate A D E X Y)
  rw [BalancedTensor.tensorHomAdjunction_homEquiv] at h
  exact ((BalancedTensor.tensorHomEquiv A (EndomorphismObject E)
    (ForgetEnrichment.of (Complex A) (endomorphismHomRight A D E Y))
    (endomorphismHomLeft A D E X) (homObject A D X Y)).symm_apply_apply
      (endomorphismEvaluation A D E X Y)).symm.trans h

end SerrePositivity.DifferentialGraded
end

end EvaluationAdjunction

/-! ## LargeHomBimodule（旧 SerrePositivity/DifferentialGraded/Endomorphism/LargeHomBimodule.lean） -/

/-! # 対象型のsmall性を仮定しない指定対象からのHom bimodule

End(E)の一対象型だけがsmallであればよい。YonedaのHom endを大きいD上に取らず、
代表加群のE成分を直接用いる。
-/

@[expose] public section LargeHomBimodule
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (E : D)

/-- Yoneda拡張のE成分は共変representable Hom(E,−)の全次数写像。 -/
lemma endomorphismYonedaApp (X Y : D) :
    yonedaExtensionApp A X (representable A Y) (𝟙 _) (op E) =
      (leftRepresentable A E).map X Y := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Cochain.ext
  intro r n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  rw [yonedaExtensionApp_apply]
  change (p * r).negOnePow • forward A h f hn =
    leftAction A (leftRepresentable A E) f h hn
  exact (leftRepresentable_action A E X Y f h hn).symm

/-- 大きい対象型でも定義できる、右End(E)加群間の全次数自然族。 -/
def largeEndomorphismHomParam (X Y : D) :
    ModuleParamTrans A (EndomorphismObject E) (X ⟶[Complex A] Y)
      (endomorphismHomRight A D E X) (endomorphismHomRight A D E Y) where
  app _ := yonedaExtensionApp A X (representable A Y) (𝟙 _) (op E)
  naturality x y := by
    change (β_ (X ⟶[Complex A] Y) (op E ⟶[Complex A] op E)).hom ≫
      ((𝟙 _ ≫ (representable A X).map (op E) (op E)) ⊗ₘ
        yonedaExtensionApp A X (representable A Y) (𝟙 _) (op E)) ≫ enrichedComposition _ _ _ =
      (yonedaExtensionApp A X (representable A Y) (𝟙 _) (op E) ⊗ₘ
        (𝟙 _ ≫ (representable A Y).map (op E) (op E))) ≫ enrichedComposition _ _ _
    simp only [Category.id_comp]
    exact yonedaExtensionApp_naturality A X (representable A Y) (𝟙 _) (op E) (op E)

/-- 大きいDに対するHom(E,−)。Small Dを仮定せずに全Hom自然性を保つ。 -/
def largeEndomorphismHomBimodule : Bimodule A (EndomorphismObject E) D :=
  Bimodule.ofParamTrans A _ D (endomorphismHomRight A D E)
    (largeEndomorphismHomParam A D E)
    (by
      intro X b
      change eId (Complex A) X ≫ yonedaExtensionApp A X (representable A X) (𝟙 _) (op E) = _
      rw [endomorphismYonedaApp]
      exact (leftRepresentable A E).map_id X)
    (by
      intro X Y Z b
      change eComp (Complex A) X Y Z ≫
        yonedaExtensionApp A X (representable A Z) (𝟙 _) (op E) =
        (yonedaExtensionApp A X (representable A Y) (𝟙 _) (op E) ⊗ₘ
          yonedaExtensionApp A Y (representable A Z) (𝟙 _) (op E)) ≫ enrichedComposition _ _ _
      rw [endomorphismYonedaApp, endomorphismYonedaApp, endomorphismYonedaApp]
      exact (leftRepresentable A E).map_comp X Y Z)

/-- smallな場合、既存Yoneda制限による構成と一致する。 -/
lemma largeEndomorphismHomBimodule_eq [Small.{u} D] :
    largeEndomorphismHomBimodule A D E = endomorphismHomBimodule A D E := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (largeEndomorphismHomBimodule A D E).toFunctor)
    (G := (endomorphismHomBimodule A D E).toFunctor) (fun _ => rfl)
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  apply moduleHom_ext
  intro b
  change (moduleHomEquiv A (EndomorphismObject E) _
      (endomorphismHomRight A D E X) (endomorphismHomRight A D E Y)).symm
        (largeEndomorphismHomParam A D E X Y) ≫ moduleHomπ A _ _ _ b =
    (moduleHomEquiv A (EndomorphismObject E) _
      (endomorphismHomRight A D E X) (endomorphismHomRight A D E Y)).symm
        (endomorphismHomParam A D E X Y) ≫ moduleHomπ A _ _ _ b
  rw [moduleHomEquiv_symm_π, moduleHomEquiv_symm_π]
  exact (yonedaHom_π A D X Y E).symm

end SerrePositivity.DifferentialGraded
end

end LargeHomBimodule

/-! ## ModuleComparison（旧 SerrePositivity/DifferentialGraded/Endomorphism/ModuleComparison.lean） -/

/-! # 実際のdg加群EによるHomとtensorの比較関手

全右加群の対象型をsmallとは仮定しない。随伴性と導来化は別の証明義務。
-/

@[expose] public section ModuleComparison
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- 全加群dg圏上のHom(E,−)関手。Hom(E,M)は元の全Hom end。 -/
def endomorphismModuleHom : DGFunctor A (RightModule A D)
    (RightModule A (EndomorphismObject E)) :=
  (largeEndomorphismHomBimodule A (RightModule A D) E).toFunctor

/-- Eに残る右D・左End(E)作用。閉零自己射だけに制限しない。 -/
def endomorphismModuleAction : Bimodule A D (EndomorphismObject E) :=
  endomorphismInclusion A E

/-- 右End(E)加群をEとtensorする、全次数自然な再構成側のdg関手。 -/
def endomorphismModuleTensor : DGFunctor A (RightModule A (EndomorphismObject E))
    (RightModule A D) :=
  (BimoduleTensor.compose A D (EndomorphismObject E) (RightModule A (EndomorphismObject E))
    (endomorphismModuleAction A D E)
    (DGFunctor.id (RightModule A (EndomorphismObject E)))).toFunctor

/-- Hom側の値は全Hom endである。 -/
lemma endomorphismModuleHom_value (M : RightModule A D) (b : EndomorphismObject E) :
    ((endomorphismModuleHom A D E).obj M).obj (op b) = moduleHom A D E M := rfl

/-- tensor側の値は既存のbalanced tensorを使う。 -/
lemma endomorphismModuleTensor_value (M : RightModule A (EndomorphismObject E)) (d : D) :
    ((endomorphismModuleTensor A D E).obj M).obj (op d) =
      BalancedTensor.obj A (EndomorphismObject E) M ((endomorphismModuleAction A D E).leftAt d) :=
  rfl

/-- 指定対象のHom像は正則End(E)加群。全加群型のsmall性は不要。 -/
lemma endomorphismModuleHom_self :
    (endomorphismModuleHom A D E).obj E =
      representable A (EndomorphismObject.point (E := E)) :=
  endomorphismHomRight_self A (RightModule A D) E

/-- 正則End(E)加群のtensor像は元のEに戻る。既存Yoneda tensor単位との比較。 -/
def endomorphismModuleTensor_regularIso :
    ForgetEnrichment.of (Complex A)
        ((endomorphismModuleTensor A D E).obj
          (representable A (EndomorphismObject.point (E := E)))) ≅
      ForgetEnrichment.of (Complex A) E :=
  BimoduleTensor.rightUnitIso A D (EndomorphismObject E)
    (endomorphismModuleAction A D E) .point

/-- U13の指定perfect対象から得るtensor側。Eは実際のdg加群として保持する。 -/
abbrev perfectEndomorphismModuleTensor (S : Set D) (E : PerfectDGModuleOver A D S) :=
  endomorphismModuleTensor A D E.val

end SerrePositivity.DifferentialGraded
end

end ModuleComparison

/-! ## ModuleFunctorMaps（旧 SerrePositivity/DifferentialGraded/Endomorphism/ModuleFunctorMaps.lean） -/

/-! # 再構成Hom・tensor関手の全Hom写像の計算

単位・余単位の自然性に用いる。閉零の式も全Hom写像から取り出す。
-/

@[expose] public section ModuleFunctorMaps
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- 再構成Hom関手の全Hom写像をEnd(E)の一対象で評価する。 -/
lemma endomorphismModuleHom_map_π (M M' : RightModule A D) :
    (endomorphismModuleHom A D E).map M M' ≫
      moduleHomπ A (EndomorphismObject E) ((endomorphismModuleHom A D E).obj M)
        ((endomorphismModuleHom A D E).obj M') .point =
      (leftRepresentable A E).map M M' := by
  change (moduleHomEquiv A (EndomorphismObject E) _ _ _).symm
    (largeEndomorphismHomParam A (RightModule A D) E M M') ≫ _ = _
  exact (moduleHomEquiv_symm_π A (EndomorphismObject E) _
    (endomorphismHomRight A (RightModule A D) E M)
    (endomorphismHomRight A (RightModule A D) E M')
    (largeEndomorphismHomParam A (RightModule A D) E M M') .point).trans
      (endomorphismYonedaApp A (RightModule A D) E M M')

/-- Hom関手の斉次作用はEndにおける前合成と逆向きの後合成。 -/
lemma endomorphismModuleHom_map_element (M M' : RightModule A D) {p r n : ℤ}
    (f : (moduleHom A D M M').X p) (m : (moduleHom A D E M).X r) (hn : r + p = n) :
    ((moduleHomπ A (EndomorphismObject E) ((endomorphismModuleHom A D E).obj M)
        ((endomorphismModuleHom A D E).obj M') .point).f p
      (((endomorphismModuleHom A D E).map M M').f p f)).v r n hn m =
    (p * r).negOnePow • forward A (D := RightModule A D) (x := E) (y := M) (z := M') m f hn := by
  have h := congrArg (fun k => (k.f p f).v r n hn m)
    (endomorphismModuleHom_map_π A D E M M')
  exact h.trans (leftRepresentable_action A E M M' f m hn)

/-- 再構成tensor関手のD成分は既存balanced tensorの右Hom写像。 -/
lemma endomorphismModuleTensor_map_π (N N' : RightModule A (EndomorphismObject E)) (d : D) :
    (endomorphismModuleTensor A D E).map N N' ≫
      moduleHomπ A D ((endomorphismModuleTensor A D E).obj N)
        ((endomorphismModuleTensor A D E).obj N') d =
    BalancedTensor.rightHomMap A (EndomorphismObject E) N N'
      ((endomorphismModuleAction A D E).leftAt d) := by
  have h := BimoduleTensor.compose_leftMap_π A D (EndomorphismObject E)
    (RightModule A (EndomorphismObject E)) (endomorphismModuleAction A D E)
    (DGFunctor.id (RightModule A (EndomorphismObject E))) N N' d
  change (endomorphismModuleTensor A D E).map N N' ≫
      moduleHomπ A D ((endomorphismModuleTensor A D E).obj N)
        ((endomorphismModuleTensor A D E).obj N') d =
    𝟙 _ ≫ BalancedTensor.rightHomMap A (EndomorphismObject E) N N'
      ((endomorphismModuleAction A D E).leftAt d) at h
  exact h.trans (Category.id_comp _)

/-- 再構成tensorの全Hom写像の生成元公式。 -/
lemma endomorphismModuleTensor_map_element (N N' : RightModule A (EndomorphismObject E))
    (d : D) {p r s a l n : ℤ} (f : (moduleHom A (EndomorphismObject E) N N').X p)
    (m : (N.obj (op (.point : EndomorphismObject E))).X r) (t : (E.obj (op d)).X s)
    (ha : r + s = a) (hl : p + r = l) (hn : a + p = n) :
    ((moduleHomπ A D ((endomorphismModuleTensor A D E).obj N)
        ((endomorphismModuleTensor A D E).obj N') d).f p
      (((endomorphismModuleTensor A D E).map N N').f p f)).v a n hn
        (BalancedTensor.element A (EndomorphismObject E) N
          ((endomorphismModuleAction A D E).leftAt d) .point m t ha) =
    BalancedTensor.element A (EndomorphismObject E) N'
      ((endomorphismModuleAction A D E).leftAt d) .point
        (((moduleHomπ A (EndomorphismObject E) N N' .point).f p f).v r l (by omega) m) t
        (by omega) := by
  have h := congrArg (fun k => (k.f p f).v a n hn
    (BalancedTensor.element A (EndomorphismObject E) N
      ((endomorphismModuleAction A D E).leftAt d) .point m t ha))
    (endomorphismModuleTensor_map_π A D E N N' d)
  exact h.trans (BalancedTensor.rightHomMap_element_of_sum A (EndomorphismObject E)
    ((endomorphismModuleAction A D E).leftAt d) f .point m t ha hl hn)

/-- 再構成tensorの閉零射は、D成分ごとに既存balanced tensorの閉零射となる。 -/
lemma endomorphismModuleTensor_map_eval {N N' : ModuleCategory A (EndomorphismObject E)}
    (f : N ⟶ N') (d : D) :
    (moduleEvaluation A D d).map ((endomorphismModuleTensor A D E).onClosed.map f) =
      BalancedTensor.rightTensorMap A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d) f := by
  apply Cochain.ofHom_injective
  rw [moduleEvaluation_cochain]
  change (moduleHomπ A D _ _ d).f 0
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f ≫
      (endomorphismModuleTensor A D E).map _ _)).val = _
  rw [cycleFromUnit_postcomp]
  have h := congrArg (fun k => k.f 0 (cycleFromUnit _
    (ForgetEnrichment.homTo (Complex A) f)).val)
      (endomorphismModuleTensor_map_π A D E
        (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) N') d)
  exact h.trans (BalancedTensor.rightHomMap_closedElement A (EndomorphismObject E)
    ((endomorphismModuleAction A D E).leftAt d) f)

/-- tensor関手の閉零射は生成元のEnd加群成分だけを動かす。 -/
lemma endomorphismModuleTensor_map_eval_element {N N' : ModuleCategory A (EndomorphismObject E)}
    (f : N ⟶ N') (d : D) {r s n : ℤ}
    (m : ((ForgetEnrichment.to (Complex A) N).obj (op (.point : EndomorphismObject E))).X r)
    (t : (E.obj (op d)).X s) (hn : r + s = n) :
    ((moduleEvaluation A D d).map ((endomorphismModuleTensor A D E).onClosed.map f)).f n
      (BalancedTensor.element A (EndomorphismObject E) (ForgetEnrichment.to (Complex A) N)
        ((endomorphismModuleAction A D E).leftAt d) .point m t hn) =
    BalancedTensor.element A (EndomorphismObject E) (ForgetEnrichment.to (Complex A) N')
      ((endomorphismModuleAction A D E).leftAt d) .point
        (((moduleEvaluation A (EndomorphismObject E) .point).map f).f r m) t hn := by
  have h := congrArg (fun k => k.f n
    (BalancedTensor.element A (EndomorphismObject E) (ForgetEnrichment.to (Complex A) N)
      ((endomorphismModuleAction A D E).leftAt d) .point m t hn))
        (endomorphismModuleTensor_map_eval A D E f d)
  exact h.trans (BalancedTensor.rightTensorMap_element A (EndomorphismObject E)
    ((endomorphismModuleAction A D E).leftAt d) f .point m t hn)

/-- Hom関手の閉零射を全Hom要素とEの元で評価すると、元の加群射の後合成になる。 -/
lemma endomorphismModuleHom_map_eval_apply (M M' : RightModule A D)
    (f : ForgetEnrichment.of (Complex A) M ⟶ ForgetEnrichment.of (Complex A) M') (d : D)
    {r s n : ℤ} (m : (moduleHom A D E M).X r) (t : (E.obj (op d)).X s) (hn : s + r = n) :
    ((moduleHomπ A D E M' d).f r
      (((moduleEvaluation A (EndomorphismObject E) .point).map
        ((endomorphismModuleHom A D E).onClosed.map f)).f r m)).v s n hn t =
    ((moduleEvaluation A D d).map f).f n (((moduleHomπ A D E M d).f r m).v s n hn t) := by
  have hc := moduleEvaluation_cochain A (EndomorphismObject E) .point
    ((endomorphismModuleHom A D E).onClosed.map f)
  change Cochain.ofHom ((moduleEvaluation A (EndomorphismObject E) .point).map
      ((endomorphismModuleHom A D E).onClosed.map f)) =
    (moduleHomπ A (EndomorphismObject E) ((endomorphismModuleHom A D E).obj M)
      ((endomorphismModuleHom A D E).obj M') .point).f 0
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f ≫
          (endomorphismModuleHom A D E).map M M')).val at hc
  rw [cycleFromUnit_postcomp] at hc
  have he := congrArg (fun c => c.v r r (add_zero r) m) hc
  rw [Cochain.ofHom_v] at he
  have hm := endomorphismModuleHom_map_element A D E M M'
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) f)).val m (add_zero r)
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at hm
  have hv := congrArg (fun z => ((moduleHomπ A D E M' d).f r z).v s n hn t) (he.trans hm)
  rw [moduleHomForward_π, Cochain.units_smul_v,
    Cochain.comp_v _ _ _ s n n hn (add_zero n)] at hv
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at hv
  have hf := congrArg (fun c => c.v n n (add_zero n)
    (((moduleHomπ A D E M d).f r m).v s n hn t)) (moduleEvaluation_cochain A D d f)
  rw [Cochain.ofHom_v] at hf
  exact hv.trans hf.symm

end SerrePositivity.DifferentialGraded
end

end ModuleFunctorMaps

/-! ## ModuleTensorElements（旧 SerrePositivity/DifferentialGraded/Endomorphism/ModuleTensorElements.lean） -/

/-! # 再構成tensorに残るD作用の生成元公式 -/

@[expose] public section ModuleTensorElements
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- End(E)作用bimoduleの転置を評価すると、元のEの右D作用になる。 -/
lemma endomorphismModuleAction_transpose (x y : Dᵒᵖ) :
    (endomorphismModuleAction A D E).transposeHom x y ≫
      leftModuleHomπ A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt x.unop)
        ((endomorphismModuleAction A D E).leftAt y.unop) .point = E.map x y :=
  (endomorphismModuleAction A D E).transposeHom_π x y .point

/-- 再構成tensorの右D作用。次数pの作用は次数rのEnd加群成分を越える符号を持つ。 -/
lemma endomorphismModuleTensor_action_element
    (N : RightModule A (EndomorphismObject E)) (x y : Dᵒᵖ)
    {p r s n : ℤ} (f : GradedHom A x y p)
    (m : (N.obj (op (.point : EndomorphismObject E))).X r) (t : (E.obj x).X s)
    (hn : r + s + p = n) :
    moduleAction A ((endomorphismModuleTensor A D E).obj N) f
      (BalancedTensor.element A (EndomorphismObject E) N
        ((endomorphismModuleAction A D E).leftAt x.unop) .point m t rfl) hn =
    (p * r).negOnePow • BalancedTensor.element A (EndomorphismObject E) N
      ((endomorphismModuleAction A D E).leftAt y.unop) .point m
        (moduleAction A E f t (by omega : s + p = p + s)) (by omega) := by
  change (((BalancedTensor.leftHomMap A (EndomorphismObject E) N
      ((endomorphismModuleAction A D E).leftAt x.unop)
      ((endomorphismModuleAction A D E).leftAt y.unop)).f p
        (((endomorphismModuleAction A D E).transposeHom x y).f p f)).v (r + s) n hn) _ = _
  rw [BalancedTensor.leftHomMap_element]
  have h := congrArg (fun k => k.f p f) (endomorphismModuleAction_transpose A D E x y)
  change (leftModuleHomπ A (EndomorphismObject E)
      ((endomorphismModuleAction A D E).leftAt x.unop)
      ((endomorphismModuleAction A D E).leftAt y.unop) .point).f p
        (((endomorphismModuleAction A D E).transposeHom x y).f p f) = (E.map x y).f p f at h
  rw [h]
  rfl

/-- 入力tensorの総次数を別名にしたD作用の生成元公式。 -/
lemma endomorphismModuleTensor_action_element_of_sum
    (N : RightModule A (EndomorphismObject E)) (x y : Dᵒᵖ)
    {p r s a n : ℤ} (f : GradedHom A x y p)
    (m : (N.obj (op (.point : EndomorphismObject E))).X r) (t : (E.obj x).X s)
    (ha : r + s = a) (hn : a + p = n) :
    moduleAction A ((endomorphismModuleTensor A D E).obj N) (x := x) (y := y) f
      (BalancedTensor.element A (EndomorphismObject E) N
        ((endomorphismModuleAction A D E).leftAt x.unop) .point m t ha) hn =
    (p * r).negOnePow • BalancedTensor.element A (EndomorphismObject E) N
      ((endomorphismModuleAction A D E).leftAt y.unop) .point m
        (moduleAction A E (x := x) (y := y) f t (rfl : s + p = s + p)) (by omega) := by
  change (((BalancedTensor.leftHomMap A (EndomorphismObject E) N
      ((endomorphismModuleAction A D E).leftAt x.unop)
      ((endomorphismModuleAction A D E).leftAt y.unop)).f p
        (((endomorphismModuleAction A D E).transposeHom x y).f p f)).v a n hn) _ = _
  have he := BalancedTensor.leftHomMap_element_of_sum A (EndomorphismObject E) N
    (N := (endomorphismModuleAction A D E).leftAt x.unop)
    (N' := (endomorphismModuleAction A D E).leftAt y.unop)
    (((endomorphismModuleAction A D E).transposeHom x y).f p f) .point m t ha
      (by omega : p + s = s + p) hn
  have h := congrArg (fun k => k.f p f) (endomorphismModuleAction_transpose A D E x y)
  change (leftModuleHomπ A (EndomorphismObject E)
      ((endomorphismModuleAction A D E).leftAt x.unop)
      ((endomorphismModuleAction A D E).leftAt y.unop) .point).f p
        (((endomorphismModuleAction A D E).transposeHom x y).f p f) = (E.map x y).f p f at h
  have hv := congrArg (fun c => c.v s (s + p) rfl t) h
  exact he.trans (congrArg (fun z => (p * r).negOnePow •
    BalancedTensor.element A (EndomorphismObject E) N
      ((endomorphismModuleAction A D E).leftAt y.unop) .point m z (by omega : r + (s + p) = n)) hv)

end SerrePositivity.DifferentialGraded
end

end ModuleTensorElements

/-! ## ModuleEvaluation（旧 SerrePositivity/DifferentialGraded/Endomorphism/ModuleEvaluation.lean） -/

/-! # 再構成tensorから元のdg加群への評価射

各D成分のbalanced評価を、全次数のD自然性を持つ実際のdg加群射に組み立てる。
-/

@[expose] public section ModuleEvaluation
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E M : RightModule A D)

/-- End(E)でbalancedな、Eの各成分におけるHomの評価。 -/
def endomorphismModuleEvaluationFamily (d : D) :
    BalancedTensor.BalancedFamily A (EndomorphismObject E)
      ((endomorphismModuleHom A D E).obj M) ((endomorphismModuleAction A D E).leftAt d)
      (M.obj (op d)) := by
  apply BalancedTensor.balancedFamilyMk A (EndomorphismObject E)
    (M := (endomorphismModuleHom A D E).obj M)
    (N := (endomorphismModuleAction A D E).leftAt d)
    (fun _ => uncurryRight (moduleHomπ A D E M d))
  intro x y r p s n hn m f t
  change (moduleHom A D E M).X r at m
  change (moduleHom A D E E).X p at f
  change (E.obj (op d)).X s at t
  change (r * p).negOnePow • (uncurryRight (moduleHomπ A D E M d)).f n
    (ιTensorObj (moduleHom A D E M) (E.obj (op d)) (r + p) s n hn
      (moduleAction A ((endomorphismModuleHom A D E).obj M)
        (x := op y) (y := op x) f m rfl ⊗ₜ[A] t)) =
    (uncurryRight (moduleHomπ A D E M d)).f n
      (ιTensorObj (moduleHom A D E M) (E.obj (op d)) r (p + s) n (by omega)
        (m ⊗ₜ[A] leftAction A ((endomorphismModuleAction A D E).leftAt d)
          (x := x) (y := y) f t (by omega)))
  rw [uncurryRight_apply, uncurryRight_apply]
  change (r * p).negOnePow •
      ((moduleHomπ A D E M d).f (r + p)
        (forward A (D := RightModule A D) (x := E) (y := E) (z := M) f m (by omega))).v
          s n (by omega) t =
    ((moduleHomπ A D E M d).f r m).v (p + s) n (by omega)
      (((moduleHomπ A D E E d).f p f).v s (p + s) (by omega) t)
  rw [moduleHomForward_π, Cochain.units_smul_v,
    Cochain.comp_v _ _ _ s (p + s) n (by omega) (by omega)]
  change (r * p).negOnePow • ((p * r).negOnePow •
    (((moduleHomπ A D E M d).f r m).v (p + s) n (by omega)
      (((moduleHomπ A D E E d).f p f).v s (p + s) (by omega) t))) = _
  rw [mul_comm r p, smul_smul, Int.units_mul_self, one_smul]

/-- 各D成分での再構成評価。 -/
def endomorphismModuleEvaluationComponent (d : D) :
    ((endomorphismModuleTensor A D E).obj ((endomorphismModuleHom A D E).obj M)).obj (op d) ⟶
      M.obj (op d) :=
  BalancedTensor.desc A _ _ _ (endomorphismModuleEvaluationFamily A D E M d)

lemma endomorphismModuleEvaluation_element (d : D) {r s n : ℤ}
    (m : (moduleHom A D E M).X r) (t : (E.obj (op d)).X s) (hn : r + s = n) :
    (endomorphismModuleEvaluationComponent A D E M d).f n
      (BalancedTensor.element A (EndomorphismObject E) ((endomorphismModuleHom A D E).obj M)
        ((endomorphismModuleAction A D E).leftAt d) .point m t hn) =
      ((moduleHomπ A D E M d).f r m).v s n (by omega) t := by
  have h := BalancedTensor.element_postcompose A (EndomorphismObject E)
    ((endomorphismModuleHom A D E).obj M) ((endomorphismModuleAction A D E).leftAt d) .point
    (endomorphismModuleEvaluationComponent A D E M d) (uncurryRight (moduleHomπ A D E M d))
    (BalancedTensor.ι_desc A _ _ _ (endomorphismModuleEvaluationFamily A D E M d) .point) m t hn
  exact h.trans (uncurryRight_apply (moduleHomπ A D E M d) r s n hn m t)

/-- Hom endの自然性による、評価とD作用の交換式。 -/
lemma endomorphismModuleEvaluation_action (x y : Dᵒᵖ) {p r s n : ℤ}
    (f : GradedHom A x y p) (m : (moduleHom A D E M).X r) (t : (E.obj x).X s)
    (hn : r + s + p = n) :
    (p * r).negOnePow • ((moduleHomπ A D E M y.unop).f r m).v (p + s) n (by omega)
        (moduleAction A E (x := x) (y := y) f t (by omega)) =
      moduleAction A M (x := x) (y := y) f
        (((moduleHomπ A D E M x.unop).f r m).v s (r + s) (by omega) t) (by omega) := by
  have h := congrArg (fun c => c.v s n (by omega) t)
    (moduleHomElement_naturality A D r m x y p f)
  rw [Cochain.comp_v _ _ _ s (p + s) n (by omega) (by omega), Cochain.units_smul_v,
    Cochain.comp_v _ _ _ s (r + s) n (by omega) (by omega)] at h
  change ((moduleHomπ A D E M y.unop).f r m).v (p + s) n (by omega)
      (moduleAction A E (x := x) (y := y) f t (by omega)) =
    (r * p).negOnePow • moduleAction A M (x := x) (y := y) f
      (((moduleHomπ A D E M x.unop).f r m).v s (r + s) (by omega) t) (by omega) at h
  rw [h, mul_comm p r, smul_smul, Int.units_mul_self, one_smul]

/-- 各成分の評価は全次数のD作用に関して自然。 -/
lemma endomorphismModuleEvaluation_naturality (x y : Dᵒᵖ) :
    ((endomorphismModuleTensor A D E).obj ((endomorphismModuleHom A D E).obj M)).map x y ≫
        homPostcompose _ (endomorphismModuleEvaluationComponent A D E M y.unop) =
      M.map x y ≫ homPrecompose (endomorphismModuleEvaluationComponent A D E M x.unop) _ := by
  apply BalancedTensor.homMap_post_pre_eq A (EndomorphismObject E)
    ((endomorphismModuleHom A D E).obj M) ((endomorphismModuleAction A D E).leftAt x.unop)
  intro p f b r s a n ha hn m t
  cases b
  subst a
  change (moduleHom A D E M).X r at m
  change (E.obj x).X s at t
  change (endomorphismModuleEvaluationComponent A D E M y.unop).f n
    (moduleAction A ((endomorphismModuleTensor A D E).obj ((endomorphismModuleHom A D E).obj M))
      (x := x) (y := y) f (BalancedTensor.element A _ _ _ .point m t rfl) hn) = _
  have h := congrArg (fun z => (endomorphismModuleEvaluationComponent A D E M y.unop).f n z)
    (endomorphismModuleTensor_action_element A D E ((endomorphismModuleHom A D E).obj M)
      x y f m t hn)
  refine h.trans ?_
  simp only [Units.smul_def, map_zsmul]
  change (p * r).negOnePow • (endomorphismModuleEvaluationComponent A D E M y.unop).f n
      (BalancedTensor.element A _ _ _ .point m (moduleAction A E f t (by omega)) (by omega)) = _
  have he := endomorphismModuleEvaluation_element A D E M y.unop m
    (moduleAction A E (x := x) (y := y) f t (by omega : s + p = p + s)) (by omega : r + (p + s) = n)
  have hi := endomorphismModuleEvaluation_element A D E M x.unop m t rfl
  exact ((congrArg (fun z => (p * r).negOnePow • z) he).trans
    (endomorphismModuleEvaluation_action A D E M x y f m t hn)).trans
      (congrArg (fun z => moduleAction A M (x := x) (y := y) f z hn) hi.symm)

/-- 再構成tensorからMへの実際の閉零dg加群射。 -/
def endomorphismModuleEvaluation :
    ForgetEnrichment.of (Complex A)
      ((endomorphismModuleTensor A D E).obj ((endomorphismModuleHom A D E).obj M)) ⟶
        ForgetEnrichment.of (Complex A) M :=
  moduleMorphismMk A D (fun d => endomorphismModuleEvaluationComponent A D E M d.unop)
    (endomorphismModuleEvaluation_naturality A D E M)

@[simp]
lemma endomorphismModuleEvaluation_eval (d : D) :
    (moduleEvaluation A D d).map (endomorphismModuleEvaluation A D E M) =
      endomorphismModuleEvaluationComponent A D E M d :=
  moduleMorphismMk_eval A D _ _ d

end SerrePositivity.DifferentialGraded
end

end ModuleEvaluation

/-! ## ModuleInsertion（旧 SerrePositivity/DifferentialGraded/Endomorphism/ModuleInsertion.lean） -/

/-! # 再構成随伴の単位を与えるdg加群射

Nの元mを、Eの元tにm⊗tを対応させる全次数自然なHom要素へ送る。
-/

@[expose] public section ModuleInsertion
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D) (N : RightModule A (EndomorphismObject E))

/-- tensorへの挿入をEの全Homに転置するためのD自然族。 -/
def endomorphismModuleInsertionParam :
    ModuleParamTrans A D (N.obj (op (.point : EndomorphismObject E))) E
      ((endomorphismModuleTensor A D E).obj N) where
  app d := curryRight (BalancedTensor.ι A (EndomorphismObject E) N
    ((endomorphismModuleAction A D E).leftAt d.unop) .point)
  naturality x y := by
    apply moduleParamNaturality_of_apply A
    intro x y k p r n hn m f t
    change BalancedTensor.element A (EndomorphismObject E) N
        ((endomorphismModuleAction A D E).leftAt y.unop) .point m
          (moduleAction A E (x := x) (y := y) f t rfl) (by omega) =
      (k * p).negOnePow • moduleAction A ((endomorphismModuleTensor A D E).obj N)
        (x := x) (y := y) f
          (BalancedTensor.element A (EndomorphismObject E) N
            ((endomorphismModuleAction A D E).leftAt x.unop) .point m t (by omega)) (by omega)
    have h := endomorphismModuleTensor_action_element_of_sum A D E N x y
      (p := p) (r := k) (s := r) (a := r + k) (n := n) f m t
      (by omega : k + r = r + k) (by omega : r + k + p = n)
    have he := congrArg (fun z => (k * p).negOnePow • z) h
    rw [mul_comm p k, smul_smul, Int.units_mul_self, one_smul] at he
    exact he.symm

/-- 挿入の全Hom endへの持ち上げ。 -/
def endomorphismModuleInsertionHom :
    N.obj (op (.point : EndomorphismObject E)) ⟶
      moduleHom A D E ((endomorphismModuleTensor A D E).obj N) :=
  (moduleHomEquiv A D _ E _).symm (endomorphismModuleInsertionParam A D E N)

@[reassoc]
lemma endomorphismModuleInsertionHom_π (d : D) :
    endomorphismModuleInsertionHom A D E N ≫
      moduleHomπ A D E ((endomorphismModuleTensor A D E).obj N) d =
    curryRight (BalancedTensor.ι A (EndomorphismObject E) N
      ((endomorphismModuleAction A D E).leftAt d) .point) :=
  moduleHomEquiv_symm_π A D _ _ _ _ d

/-- 挿入の純粋斉次元公式。 -/
lemma endomorphismModuleInsertionHom_element (d : D) {r s n : ℤ}
    (m : (N.obj (op (.point : EndomorphismObject E))).X r) (t : (E.obj (op d)).X s)
    (hn : s + r = n) :
    ((moduleHomπ A D E ((endomorphismModuleTensor A D E).obj N) d).f r
      ((endomorphismModuleInsertionHom A D E N).f r m)).v s n hn t =
      BalancedTensor.element A (EndomorphismObject E) N
        ((endomorphismModuleAction A D E).leftAt d) .point m t (by omega) := by
  have h := congrArg (fun k => (k.f r m).v s n hn t)
    (endomorphismModuleInsertionHom_π A D E N d)
  exact h

/-- 挿入はEnd(E)作用と可換である。balanced関係を転置した式。 -/
lemma endomorphismModuleInsertionHom_action (x y : (EndomorphismObject E)ᵒᵖ)
    (p r n : ℤ) (hn : r + p = n) (f : GradedHom A x y p) (m : (N.obj x).X r) :
    (endomorphismModuleInsertionHom A D E N).f n (moduleAction A N (x := x) (y := y) f m hn) =
      moduleAction A ((endomorphismModuleHom A D E).obj ((endomorphismModuleTensor A D E).obj N))
        (x := x) (y := y) f ((endomorphismModuleInsertionHom A D E N).f r m) hn := by
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  cases x
  cases y
  apply moduleHomElement_ext A D
  intro d
  apply Cochain.ext
  intro s l hl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  change ((moduleHomπ A D E ((endomorphismModuleTensor A D E).obj N) d).f n
      ((endomorphismModuleInsertionHom A D E N).f n (moduleAction A N f m hn))).v s l hl t =
    ((moduleHomπ A D E ((endomorphismModuleTensor A D E).obj N) d).f n
      (forward A (D := RightModule A D) (x := E) (y := E)
        (z := (endomorphismModuleTensor A D E).obj N) f
          ((endomorphismModuleInsertionHom A D E N).f r m) (by omega))).v s l hl t
  rw [moduleHomForward_π, Cochain.units_smul_v,
    Cochain.comp_v _ _ _ s (p + s) l (by omega) (by omega)]
  change _ = (p * r).negOnePow •
    ((moduleHomπ A D E ((endomorphismModuleTensor A D E).obj N) d).f r
      ((endomorphismModuleInsertionHom A D E N).f r m)).v (p + s) l (by omega)
        (((moduleHomπ A D E E d).f p f).v s (p + s) (by omega) t)
  rw [endomorphismModuleInsertionHom_element, endomorphismModuleInsertionHom_element]
  have h := BalancedTensor.element_balanced A (EndomorphismObject E) N
    ((endomorphismModuleAction A D E).leftAt d) .point .point m f t (by omega : r + p + s = l)
  subst n
  have he := congrArg (fun z => (r * p).negOnePow • z) h
  rw [smul_smul, Int.units_mul_self, one_smul] at he
  convert! he using 1
  simp only [mul_comm p r]
  rename_i htype
  cases htype
  rfl

/-- 実際の右End(E)加群射としての挿入。 -/
def endomorphismModuleInsertion :
    ForgetEnrichment.of (Complex A) N ⟶
      ForgetEnrichment.of (Complex A)
        ((endomorphismModuleHom A D E).obj ((endomorphismModuleTensor A D E).obj N)) :=
  moduleMorphismMk A (EndomorphismObject E)
    (fun _ => endomorphismModuleInsertionHom A D E N)
    (closedFamily_of_action A _ (endomorphismModuleInsertionHom_action A D E N))

@[simp]
lemma endomorphismModuleInsertion_eval (b : EndomorphismObject E) :
    (moduleEvaluation A (EndomorphismObject E) b).map (endomorphismModuleInsertion A D E N) =
      endomorphismModuleInsertionHom A D E N := moduleMorphismMk_eval A _ _ _ b

end SerrePositivity.DifferentialGraded
end

end ModuleInsertion

/-! ## ModuleAdjunction（旧 SerrePositivity/DifferentialGraded/Endomorphism/ModuleAdjunction.lean） -/

/-! # 指定dg加群Eに対するtensor–Hom再構成随伴

全加群dg圏の対象型のsmall性を仮定せず、閉零加群圏で単位・余単位を組み立てる。
-/

@[expose] public section ModuleAdjunction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- 再構成随伴の単位。挿入射はEnd(E)加群変数にも自然。 -/
def endomorphismModuleUnit :
    𝟭 (ModuleCategory A (EndomorphismObject E)) ⟶
      (endomorphismModuleTensor A D E).onClosed ⋙ (endomorphismModuleHom A D E).onClosed where
  app N := endomorphismModuleInsertion A D E (ForgetEnrichment.to (Complex A) N)
  naturality {N N'} f := by
    apply moduleMorphism_ext
    intro b
    cases b
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      endomorphismModuleInsertion_eval, endomorphismModuleInsertion_eval]
    apply HomologicalComplex.hom_ext
    intro r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    apply moduleHomElement_ext A D
    intro d
    apply Cochain.ext
    intro s n hn
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    change ((moduleHomπ A D E
        ((endomorphismModuleTensor A D E).obj (ForgetEnrichment.to (Complex A) N')) d).f r
      ((endomorphismModuleInsertionHom A D E (ForgetEnrichment.to (Complex A) N')).f r
        (((moduleEvaluation A (EndomorphismObject E) .point).map f).f r m))).v s n hn t = _
    have hi := endomorphismModuleInsertionHom_element A D E
      (ForgetEnrichment.to (Complex A) N) d m t hn
    have hi' := endomorphismModuleInsertionHom_element A D E
      (ForgetEnrichment.to (Complex A) N') d
        (((moduleEvaluation A (EndomorphismObject E) .point).map f).f r m) t hn
    have ht := endomorphismModuleTensor_map_eval_element A D E f d m t
      (by omega : r + s = n)
    have hr := endomorphismModuleHom_map_eval_apply A D E
      ((endomorphismModuleTensor A D E).obj (ForgetEnrichment.to (Complex A) N))
      ((endomorphismModuleTensor A D E).obj (ForgetEnrichment.to (Complex A) N'))
      ((endomorphismModuleTensor A D E).onClosed.map f) d
      ((endomorphismModuleInsertionHom A D E (ForgetEnrichment.to (Complex A) N)).f r m) t hn
    exact hi'.trans (ht.symm.trans ((congrArg (fun z =>
      ((moduleEvaluation A D d).map ((endomorphismModuleTensor A D E).onClosed.map f)).f n z)
        hi.symm).trans hr.symm))

/-- 再構成随伴の余単位。評価射はD加群変数にも自然。 -/
def endomorphismModuleCounit :
    (endomorphismModuleHom A D E).onClosed ⋙ (endomorphismModuleTensor A D E).onClosed ⟶
      𝟭 (ModuleCategory A D) where
  app M := endomorphismModuleEvaluation A D E (ForgetEnrichment.to (Complex A) M)
  naturality {M M'} f := by
    apply moduleMorphism_ext
    intro d
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      endomorphismModuleEvaluation_eval, endomorphismModuleEvaluation_eval]
    apply Cochain.ofHom_injective
    apply BalancedTensor.cochain_zero_element_ext A (EndomorphismObject E)
      ((endomorphismModuleHom A D E).obj (ForgetEnrichment.to (Complex A) M))
      ((endomorphismModuleAction A D E).leftAt d)
    intro b r s n hn m t
    cases b
    simp only [Cochain.ofHom_v]
    change (endomorphismModuleEvaluationComponent A D E (ForgetEnrichment.to (Complex A) M') d).f n
      (((moduleEvaluation A D d).map ((endomorphismModuleTensor A D E).onClosed.map
        ((endomorphismModuleHom A D E).onClosed.map f))).f n
          (BalancedTensor.element A _ _ _ .point m t hn)) = _
    have ht := endomorphismModuleTensor_map_eval_element A D E
      ((endomorphismModuleHom A D E).onClosed.map f) d m t hn
    have he' := endomorphismModuleEvaluation_element A D E (ForgetEnrichment.to (Complex A) M') d
      (((moduleEvaluation A (EndomorphismObject E) .point).map
        ((endomorphismModuleHom A D E).onClosed.map f)).f r m) t hn
    have he := endomorphismModuleEvaluation_element A D E
      (ForgetEnrichment.to (Complex A) M) d m t hn
    have hr := endomorphismModuleHom_map_eval_apply A D E
      (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) M') f d m t
        (by omega : s + r = n)
    exact (congrArg (fun z =>
      (endomorphismModuleEvaluationComponent A D E (ForgetEnrichment.to (Complex A) M') d).f n z)
        ht).trans (he'.trans (hr.trans (congrArg (fun z => ((moduleEvaluation A D d).map f).f n z)
          he.symm)))

/-- 再構成tensorに関する左三角恒等式。 -/
lemma endomorphismModule_left_triangle (N : ModuleCategory A (EndomorphismObject E)) :
    (endomorphismModuleTensor A D E).onClosed.map ((endomorphismModuleUnit A D E).app N) ≫
      (endomorphismModuleCounit A D E).app
        ((endomorphismModuleTensor A D E).onClosed.obj N) = 𝟙 _ := by
  apply moduleMorphism_ext
  intro d
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  dsimp only [endomorphismModuleCounit]
  rw [endomorphismModuleEvaluation_eval]
  apply Cochain.ofHom_injective
  apply BalancedTensor.cochain_zero_element_ext A (EndomorphismObject E)
    (ForgetEnrichment.to (Complex A) N) ((endomorphismModuleAction A D E).leftAt d)
  intro b r s n hn m t
  cases b
  simp only [Cochain.ofHom_v]
  have ht := endomorphismModuleTensor_map_eval_element A D E
    ((endomorphismModuleUnit A D E).app N) d m t hn
  have hu := endomorphismModuleInsertion_eval A D E (ForgetEnrichment.to (Complex A) N) .point
  have he := endomorphismModuleEvaluation_element A D E
    ((endomorphismModuleTensor A D E).obj (ForgetEnrichment.to (Complex A) N)) d
      ((endomorphismModuleInsertionHom A D E (ForgetEnrichment.to (Complex A) N)).f r m) t hn
  have hi := endomorphismModuleInsertionHom_element A D E (ForgetEnrichment.to (Complex A) N)
    d m t (by omega : s + r = n)
  change (endomorphismModuleEvaluationComponent A D E
    ((endomorphismModuleTensor A D E).obj (ForgetEnrichment.to (Complex A) N)) d).f n
      (((moduleEvaluation A D d).map ((endomorphismModuleTensor A D E).onClosed.map
        ((endomorphismModuleUnit A D E).app N))).f n
          (BalancedTensor.element A (EndomorphismObject E) (ForgetEnrichment.to (Complex A) N)
            ((endomorphismModuleAction A D E).leftAt d) .point m t hn)) = _
  have ht' := congrArg (fun z => (endomorphismModuleEvaluationComponent A D E
    ((endomorphismModuleTensor A D E).obj (ForgetEnrichment.to (Complex A) N)) d).f n z) ht
  dsimp only [endomorphismModuleUnit] at ht'
  rw [hu] at ht'
  exact ht'.trans (he.trans hi)

/-- 再構成Homに関する右三角恒等式。 -/
lemma endomorphismModule_right_triangle (M : ModuleCategory A D) :
    (endomorphismModuleUnit A D E).app ((endomorphismModuleHom A D E).onClosed.obj M) ≫
      (endomorphismModuleHom A D E).onClosed.map
        ((endomorphismModuleCounit A D E).app M) = 𝟙 _ := by
  apply moduleMorphism_ext
  intro b
  cases b
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  apply HomologicalComplex.hom_ext
  intro r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply moduleHomElement_ext A D
  intro d
  apply Cochain.ext
  intro s n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  have hu := endomorphismModuleInsertion_eval A D E
    ((endomorphismModuleHom A D E).obj (ForgetEnrichment.to (Complex A) M)) .point
  have hi := endomorphismModuleInsertionHom_element A D E
    ((endomorphismModuleHom A D E).obj (ForgetEnrichment.to (Complex A) M)) d m t hn
  have he := endomorphismModuleEvaluation_element A D E (ForgetEnrichment.to (Complex A) M)
    d m t (by omega : r + s = n)
  have hr := endomorphismModuleHom_map_eval_apply A D E
    ((endomorphismModuleTensor A D E).obj
      ((endomorphismModuleHom A D E).obj (ForgetEnrichment.to (Complex A) M)))
    (ForgetEnrichment.to (Complex A) M) ((endomorphismModuleCounit A D E).app M) d
    ((endomorphismModuleInsertionHom A D E
      ((endomorphismModuleHom A D E).obj (ForgetEnrichment.to (Complex A) M))).f r m) t hn
  change ((moduleHomπ A D E (ForgetEnrichment.to (Complex A) M) d).f r
    (((moduleEvaluation A (EndomorphismObject E) .point).map
      ((endomorphismModuleHom A D E).onClosed.map ((endomorphismModuleCounit A D E).app M))).f r
        (((moduleEvaluation A (EndomorphismObject E) .point).map
          (endomorphismModuleInsertion A D E
            ((endomorphismModuleHom A D E).obj (ForgetEnrichment.to (Complex A) M)))).f r m))).v
              s n hn t = _
  rw [hu]
  have hc := endomorphismModuleEvaluation_eval A D E (ForgetEnrichment.to (Complex A) M) d
  dsimp only [endomorphismModuleCounit] at hr
  rw [hc] at hr
  exact hr.trans ((congrArg (fun z =>
    (endomorphismModuleEvaluationComponent A D E (ForgetEnrichment.to (Complex A) M) d).f n z)
      hi).trans he)

/-- 既存balanced tensorと全Hom endによる、指定dg加群Eの再構成随伴。 -/
def endomorphismModuleAdjunction :
    (endomorphismModuleTensor A D E).onClosed ⊣ (endomorphismModuleHom A D E).onClosed :=
  Adjunction.mkOfUnitCounit
    { unit := endomorphismModuleUnit A D E
      counit := endomorphismModuleCounit A D E
      left_triangle := by
        apply NatTrans.ext
        funext N
        simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
          Functor.associator_hom_app, Category.id_comp, Category.comp_id,
          Functor.comp_obj, Functor.id_obj, NatTrans.id] using
            endomorphismModule_left_triangle A D E N
      right_triangle := by
        apply NatTrans.ext
        funext M
        simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
          Functor.associator_inv_app, Category.id_comp, Category.comp_id,
          Functor.comp_obj, Functor.id_obj, NatTrans.id] using
            endomorphismModule_right_triangle A D E M }

end SerrePositivity.DifferentialGraded
end

end ModuleAdjunction
