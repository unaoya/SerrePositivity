module

public import SerrePositivity.DifferentialGraded.Bimodule.Basic
public import SerrePositivity.DifferentialGraded.Module.LeftClosedMaps
public import SerrePositivity.DifferentialGraded.Complexes.HomNaturalityEvaluation
public import SerrePositivity.DifferentialGraded.Module.LeftQuasiIso
public import SerrePositivity.DifferentialGraded.Functor.Opposite
public import SerrePositivity.DifferentialGraded.Module.RestrictionEnriched
public import SerrePositivity.DifferentialGraded.Complexes.HomMapEvaluation
public import SerrePositivity.DifferentialGraded.Module.RestrictionCoherence
public import SerrePositivity.DifferentialGraded.Module.LeftHomElements
public import SerrePositivity.DifferentialGraded.Module.LeftCategory
public import SerrePositivity.DifferentialGraded.Module.Action

/-!
# Bimodule.Value

## 概要
16 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

universe u v w z t

/-! ## LeftEvaluation（旧 SerrePositivity/DifferentialGraded/Bimodule/LeftEvaluation.lean） -/

/-! # 閉零bimodule射の両対象評価と左加群としての評価 -/

@[expose] public section LeftEvaluation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 両対象を固定した値の複体への評価。 -/
def valueEvaluation (b : B) (c : C) : BimoduleCategory A B C ⥤ Complex A :=
  evaluation A B C c ⋙ moduleEvaluation A B b

lemma valueMap_left_naturality {M N : BimoduleCategory A B C} (a : M ⟶ N)
    (b : B) (c c' : C) :
    ((underlying A B C M).leftAt b).map c c' ≫
      homPostcompose ((underlying A B C M).value b c)
        ((valueEvaluation A B C b c').map a) =
    ((underlying A B C N).leftAt b).map c c' ≫
      homPrecompose ((valueEvaluation A B C b c).map a)
        ((underlying A B C N).value b c') := by
  have hp := congrArg (fun k : (c ⟶[Complex A] c') ⟶
      moduleHom A B ((underlying A B C M).rightAt c)
        ((underlying A B C N).rightAt c') =>
    k ≫ moduleHomπ A B ((underlying A B C M).rightAt c)
      ((underlying A B C N).rightAt c') b) (a.property c c')
  simp only [Category.assoc] at hp
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π] at hp
  change (((underlying A B C M).toFunctor.map c c') ≫
      moduleHomπ A B ((underlying A B C M).rightAt c)
        ((underlying A B C M).rightAt c') b) ≫ _ =
    (((underlying A B C N).toFunctor.map c c') ≫
      moduleHomπ A B ((underlying A B C N).rightAt c)
        ((underlying A B C N).rightAt c') b) ≫ _
  exact (Category.assoc _ _ _).trans (hp.trans (Category.assoc _ _ _).symm)

variable [Small.{u} C]

/-- 右対象を固定した、全次数自然な左C加群への評価。 -/
def leftEvaluation (b : B) : BimoduleCategory A B C ⥤ LeftModuleCategory A C where
  obj M := ForgetEnrichment.of (Complex A) ((underlying A B C M).leftAt b)
  map a := leftModuleMorphismMk A C
    (fun c => (valueEvaluation A B C b c).map a) (valueMap_left_naturality A B C a b)
  map_id M := by
    apply leftModuleMorphism_ext A C
    intro c
    rw [leftModuleMorphismMk_eval]
    exact ((valueEvaluation A B C b c).map_id M).trans
      ((leftModuleEvaluation A C c).map_id
        (ForgetEnrichment.of (Complex A) ((underlying A B C M).leftAt b))).symm
  map_comp a d := by
    apply leftModuleMorphism_ext A C
    intro c
    rw [leftModuleMorphismMk_eval, (leftModuleEvaluation A C c).map_comp,
      leftModuleMorphismMk_eval, leftModuleMorphismMk_eval]
    exact (valueEvaluation A B C b c).map_comp a d

@[simp]
lemma leftEvaluation_map_eval {M N : BimoduleCategory A B C} (a : M ⟶ N) (b : B) (c : C) :
    (leftModuleEvaluation A C c).map ((leftEvaluation A B C b).map a) =
      (valueEvaluation A B C b c).map a :=
  leftModuleMorphismMk_eval A C
    (M := (underlying A B C M).leftAt b) (N := (underlying A B C N).leftAt b)
    (fun x => (valueEvaluation A B C b x).map a)
    (valueMap_left_naturality A B C a b) c

end SerrePositivity.DifferentialGraded.BimoduleCategory
end

end LeftEvaluation

/-! ## ValueExt（旧 SerrePositivity/DifferentialGraded/Bimodule/ValueExt.lean） -/

/-! # 閉零bimodule射の値の複体による外延性 -/

@[expose] public section ValueExt

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

lemma value_hom_ext {M N : BimoduleCategory A B C} {f g : M ⟶ N}
    (h : ∀ b c, (valueEvaluation A B C b c).map f = (valueEvaluation A B C b c).map g) :
    f = g := by
  apply hom_ext A B C
  intro c
  apply moduleMorphism_ext A B
  intro b
  exact h b c

end SerrePositivity.DifferentialGraded.BimoduleCategory
end

end ValueExt

/-! ## ValueActions（旧 SerrePositivity/DifferentialGraded/Bimodule/ValueActions.lean） -/

/-! # 閉零bimodule射の値成分と左右斉次作用の可換式 -/

@[expose] public section ValueActions

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

lemma valueMap_leftAction {M N : BimoduleCategory A B C} (a : M ⟶ N)
    (b : B) (c c' : C) {p i n : ℤ} (hn : i + p = n) (g : GradedHom A c c' p)
    (v : ((underlying A B C M).value b c).X i) :
    ((valueEvaluation A B C b c').map a).f n
      (leftAction A ((underlying A B C M).leftAt b) g v hn) =
    leftAction A ((underlying A B C N).leftAt b) g
      (((valueEvaluation A B C b c).map a).f i v) hn :=
  hom_naturality_apply (((underlying A B C M).leftAt b).map c c')
    (((underlying A B C N).leftAt b).map c c')
    ((valueEvaluation A B C b c).map a) ((valueEvaluation A B C b c').map a)
    (valueMap_left_naturality A B C a b c c') hn g v

lemma valueMap_rightAction {M N : BimoduleCategory A B C} (a : M ⟶ N)
    (b b' : Bᵒᵖ) (c : C) {p i n : ℤ} (hn : i + p = n) (g : GradedHom A b b' p)
    (v : ((underlying A B C M).value b.unop c).X i) :
    ((valueEvaluation A B C b'.unop c).map a).f n
      (moduleAction A ((underlying A B C M).rightAt c) g v hn) =
    moduleAction A ((underlying A B C N).rightAt c) g
      (((valueEvaluation A B C b.unop c).map a).f i v) hn := by
  let τ := moduleClosedHomEquiv A B ((evaluation A B C c).obj M)
    ((evaluation A B C c).obj N) ((evaluation A B C c).map a)
  exact closedFamily_action A (closedTransApp A τ) (closedTransApp_naturality A τ)
    b b' p i n hn g v

end SerrePositivity.DifferentialGraded.BimoduleCategory
end

end ValueActions

/-! ## ValueIdentity（旧 SerrePositivity/DifferentialGraded/Bimodule/ValueIdentity.lean） -/

/-! # 閉零bimodule恒等射の値の成分 -/

@[expose] public section ValueIdentity

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

lemma valueMap_id_apply (M : BimoduleCategory A B C) (b : B) (c : C) (n : ℤ)
    (v : ((underlying A B C M).value b c).X n) :
    ((valueEvaluation A B C b c).map (𝟙 M)).f n v = v :=
  (congrArg (fun k : (underlying A B C M).value b c ⟶
      (underlying A B C M).value b c => k.f n v)
    ((valueEvaluation A B C b c).map_id M)).trans (by rfl)

end SerrePositivity.DifferentialGraded.BimoduleCategory
end

end ValueIdentity

/-! ## ValueIsomorphism（旧 SerrePositivity/DifferentialGraded/Bimodule/ValueIsomorphism.lean） -/

/-! # 値の全Hom自然性から右加群同型族をbimodule同型へ束ねる

## 概要
値の全Hom自然性から右加群同型族をbimodule同型へ束ねる。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section ValueIsomorphism

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C]

lemma isoFamily_naturality_of_values {M N : BimoduleCategory A B C}
    (a : ∀ c, (evaluation A B C c).obj M ≅ (evaluation A B C c).obj N)
    (h : ∀ b c c', ((underlying A B C M).leftAt b).map c c' ≫
      homPostcompose ((underlying A B C M).value b c)
        ((moduleEvaluation A B b).map (a c').hom) =
      ((underlying A B C N).leftAt b).map c c' ≫
        homPrecompose ((moduleEvaluation A B b).map (a c).hom)
          ((underlying A B C N).value b c')) (c c' : C) :
    (underlying A B C M).map c c' ≫
      moduleHomPostcompose A B ((underlying A B C M).rightAt c)
        ((underlying A B C M).rightAt c') ((underlying A B C N).rightAt c') (a c').hom =
    (underlying A B C N).map c c' ≫
      moduleHomPrecompose A B ((underlying A B C M).rightAt c)
        ((underlying A B C N).rightAt c) ((underlying A B C N).rightAt c') (a c).hom := by
  apply moduleHom_ext
  intro b
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  have hh := h b c c'
  change (_ ≫ moduleHomπ A B _ _ b) ≫ _ = (_ ≫ moduleHomπ A B _ _ b) ≫ _ at hh
  exact (Category.assoc _ _ _).symm.trans (hh.trans (Category.assoc _ _ _))

/-- 右加群同型族の左作用との全次数自然性を、値のHom複体で確認して束ねる。 -/
def isoOfValueFamily {M N : BimoduleCategory A B C}
    (a : ∀ c, (evaluation A B C c).obj M ≅ (evaluation A B C c).obj N)
    (h : ∀ b c c', ((underlying A B C M).leftAt b).map c c' ≫
      homPostcompose ((underlying A B C M).value b c)
        ((moduleEvaluation A B b).map (a c').hom) =
      ((underlying A B C N).leftAt b).map c c' ≫
        homPrecompose ((moduleEvaluation A B b).map (a c).hom)
          ((underlying A B C N).value b c')) : M ≅ N :=
  isoOfFamily A B C a (isoFamily_naturality_of_values A B C a h)

@[simp]
lemma isoOfValueFamily_hom_eval {M N : BimoduleCategory A B C} (a) (h) (c : C) :
    (evaluation A B C c).map (isoOfValueFamily A B C (M := M) (N := N) a h).hom =
      (a c).hom := rfl

end SerrePositivity.DifferentialGraded.BimoduleCategory
end

end ValueIsomorphism

/-! ## QuasiIso（旧 SerrePositivity/DifferentialGraded/Bimodule/QuasiIso.lean） -/

/-! # 全Hom自然な閉零bimodule圏で局所化する準同型のクラス

## 概要
全Hom自然な閉零bimodule圏で局所化する準同型のクラス。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/TensorModuleComparison.lean、Derived/
BimoduleBasic.lean、Tensor/BimoduleQuasiIso.lean。局所導来合成の計算部品、一般Morita・相対tensor・
Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section QuasiIso

noncomputable section
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 両対象の各値で複体のquasiIsoとなる射。両作用の全Hom自然性は元の射が保持する。 -/
def quasiIso : MorphismProperty (BimoduleCategory A B C) :=
  fun _ _ f => ∀ (b : B) (c : C), QuasiIso ((valueEvaluation A B C b c).map f)

@[simp]
lemma quasiIso_iff {M N : BimoduleCategory A B C} (f : M ⟶ N) :
    quasiIso A B C f ↔ ∀ b c, QuasiIso ((valueEvaluation A B C b c).map f) := Iff.rfl

lemma quasiIso_eq_iInf : quasiIso A B C =
    ⨅ b : B, ⨅ c : C, (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)).inverseImage
      (valueEvaluation A B C b c) := by
  ext M N f
  simp [quasiIso, MorphismProperty.iInf_iff, MorphismProperty.inverseImage]

instance quasiIsoIsMultiplicative : (quasiIso A B C).IsMultiplicative where
  id_mem M b c := by
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  comp_mem f g hf hg b c := by
    have := hf b c
    have := hg b c
    rw [CategoryTheory.Functor.map_comp]
    infer_instance

instance quasiIsoHasTwoOutOfThree : (quasiIso A B C).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg b c := by
    have := hg b c
    have : QuasiIso ((valueEvaluation A B C b c).map f ≫
        (valueEvaluation A B C b c).map g) := by
      simpa only [← CategoryTheory.Functor.map_comp] using hfg b c
    exact quasiIso_of_comp_right _ ((valueEvaluation A B C b c).map g)
  of_precomp f g hf hfg b c := by
    have := hf b c
    have : QuasiIso ((valueEvaluation A B C b c).map f ≫
        (valueEvaluation A B C b c).map g) := by
      simpa only [← CategoryTheory.Functor.map_comp] using hfg b c
    exact quasiIso_of_comp_left ((valueEvaluation A B C b c).map f) _

instance quasiIsoStableUnderRetracts : (quasiIso A B C).IsStableUnderRetracts where
  of_retract h hg b c := by
    have := hg b c
    exact quasiIso_of_retractArrow (h.map (valueEvaluation A B C b c))

instance quasiIsoRespectsIso : (quasiIso A B C).RespectsIso := by
  rw [quasiIso_eq_iInf]
  infer_instance

lemma quasiIso_evaluation {M N : BimoduleCategory A B C} {f : M ⟶ N}
    (hf : quasiIso A B C f) (c : C) : moduleQuasiIso A B ((evaluation A B C c).map f) :=
  fun b => hf b c

variable [Small.{u} C]

lemma quasiIso_leftEvaluation {M N : BimoduleCategory A B C} {f : M ⟶ N}
    (hf : quasiIso A B C f) (b : B) :
    leftModuleQuasiIso A C ((leftEvaluation A B C b).map f) := by
  apply (leftModuleQuasiIso_iff A C _).2
  intro c
  rw [leftEvaluation_map_eval]
  exact hf b c

end SerrePositivity.DifferentialGraded.BimoduleCategory
end

end QuasiIso

/-! ## MiddleRestriction（旧 SerrePositivity/DifferentialGraded/Bimodule/MiddleRestriction.lean） -/

/-! # 合成の中間dg圏に沿うbimoduleの二つの制限

## 概要
合成の中間dg圏に沿うbimoduleの二つの制限。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section MiddleRestriction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)

/-- 中間圏が左側に現れる因子は、既存のdg関手に前合成する。 -/
def leftRestriction (P : Bimodule A B C) : Bimodule A B D := F.comp P

/-- 中間圏が右側に現れる因子は、既存の豊穣制限に後合成する。 -/
def rightRestriction (Q : Bimodule A C E) : Bimodule A D E :=
  Q.comp (dgModuleRestriction A D C F.op)

omit [Small.{u} C] [Small.{u} D] [DGCategory A E] in
lemma leftRestriction_leftAt (P : Bimodule A B C) (b : B) :
    (leftRestriction A B C D F P).leftAt b = F.comp (P.leftAt b) := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  change ((F.map x y ≫ P.map (F.obj x) (F.obj y)) ≫ moduleHomπ A B _ _ b) ≫ 𝟙 _ =
    F.map x y ≫ (P.map (F.obj x) (F.obj y) ≫ moduleHomπ A B _ _ b)
  rw [Category.comp_id, Category.assoc]

lemma rightRestriction_leftAt_map (Q : Bimodule A C E) (d : D) (e e' : E) :
    ((rightRestriction A C D E F Q).leftAt d).map e e' =
      (Q.leftAt (F.obj d)).map e e' := by
  change (Q.map e e' ≫ moduleRestrictionHom A D C F.op _ _) ≫ moduleHomπ A D _ _ d =
    Q.map e e' ≫ moduleHomπ A C _ _ (F.obj d)
  rw [Category.assoc, moduleRestrictionHom_π]
  rfl

lemma rightRestriction_leftAction (Q : Bimodule A C E) (d : D) {e e' : E} {p i n : ℤ}
    (g : GradedHom A e e' p) (q : (Q.value (F.obj d) e).X i) (hn : i + p = n) :
    leftAction A ((rightRestriction A C D E F Q).leftAt d) g q hn =
      leftAction A (Q.leftAt (F.obj d)) g q hn :=
  congrArg (fun k => (k.f p g).v i n hn q)
    (rightRestriction_leftAt_map A C D E F Q d e e')

end SerrePositivity.DifferentialGraded.Bimodule
end

end MiddleRestriction

/-! ## MiddleRestrictionMaps（旧 SerrePositivity/DifferentialGraded/Bimodule/MiddleRestrictionMaps.lean） -/

/-! # 中間dg圏への両因子の制限を全Hom自然な閉零射へ拡張する

## 概要
中間dg圏への両因子の制限を全Hom自然な閉零射へ拡張する。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section MiddleRestrictionMaps

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory Opposite
variable (A : Type u) [CommRing A]

section Left
variable (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] (D : Type z) [DGCategory A D] (F : DGFunctor A D C)

def middleLeftRestrictionMap {P P' : BimoduleCategory A B C} (f : P ⟶ P') :
    of A B D (Bimodule.leftRestriction A B C D F (underlying A B C P)) ⟶
      of A B D (Bimodule.leftRestriction A B C D F (underlying A B C P')) :=
  ⟨fun d => f.val (F.obj d), fun d d' => by
    change (F.map d d' ≫ (underlying A B C P).map (F.obj d) (F.obj d')) ≫ _ =
      (F.map d d' ≫ (underlying A B C P').map (F.obj d) (F.obj d')) ≫ _
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => F.map d d' ≫ k) (f.property (F.obj d) (F.obj d'))).trans
        (Category.assoc _ _ _).symm)⟩

@[simp]
lemma middleLeftRestrictionMap_value_eval {P P' : BimoduleCategory A B C} (f : P ⟶ P')
    (b : B) (d : D) :
    (valueEvaluation A B D b d).map (middleLeftRestrictionMap A B C D F f) =
      (valueEvaluation A B C b (F.obj d)).map f := rfl

def middleLeftRestrictionFunctor : BimoduleCategory A B C ⥤ BimoduleCategory A B D where
  obj P := of A B D (Bimodule.leftRestriction A B C D F (underlying A B C P))
  map f := middleLeftRestrictionMap A B C D F f
  map_id _ := rfl
  map_comp _ _ := rfl

end Left
section Right
variable (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)

lemma middleRightRestrictionMap_component {Q Q' : BimoduleCategory A C E} (g : Q ⟶ Q')
    (d : D) (e : E) :
    moduleMorphismComponent A D
      ((Bimodule.rightRestriction A C D E F (underlying A C E Q)).rightAt e)
      ((Bimodule.rightRestriction A C D E F (underlying A C E Q')).rightAt e)
      ((moduleRestriction A D C F.op).map (g.val e)) d =
        (valueEvaluation A C E (F.obj d) e).map g :=
  moduleRestriction_map_eval A D C F.op (g.val e) d

lemma middleRightRestrictionMap_naturality {Q Q' : BimoduleCategory A C E} (g : Q ⟶ Q')
    (e e' : E) :
    (Bimodule.rightRestriction A C D E F (underlying A C E Q)).map e e' ≫
      moduleHomPostcompose A D
        ((Bimodule.rightRestriction A C D E F (underlying A C E Q)).rightAt e)
        ((Bimodule.rightRestriction A C D E F (underlying A C E Q)).rightAt e')
        ((Bimodule.rightRestriction A C D E F (underlying A C E Q')).rightAt e')
        ((moduleRestriction A D C F.op).map (g.val e')) =
    (Bimodule.rightRestriction A C D E F (underlying A C E Q')).map e e' ≫
      moduleHomPrecompose A D
        ((Bimodule.rightRestriction A C D E F (underlying A C E Q)).rightAt e)
        ((Bimodule.rightRestriction A C D E F (underlying A C E Q')).rightAt e)
        ((Bimodule.rightRestriction A C D E F (underlying A C E Q')).rightAt e')
        ((moduleRestriction A D C F.op).map (g.val e)) := by
  apply moduleHom_ext
  intro d
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  simp only [middleRightRestrictionMap_component]
  have h := valueMap_left_naturality A C E g (F.obj d) e e'
  have hQ := Bimodule.rightRestriction_leftAt_map A C D E F (underlying A C E Q) d e e'
  have hQ' := Bimodule.rightRestriction_leftAt_map A C D E F (underlying A C E Q') d e e'
  rw [← hQ, ← hQ'] at h
  change ((Bimodule.rightRestriction A C D E F (underlying A C E Q)).map e e' ≫
      moduleHomπ A D _ _ d) ≫ _ =
    ((Bimodule.rightRestriction A C D E F (underlying A C E Q')).map e e' ≫
      moduleHomπ A D _ _ d) ≫ _ at h
  exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))

def middleRightRestrictionMap {Q Q' : BimoduleCategory A C E} (g : Q ⟶ Q') :
    of A D E (Bimodule.rightRestriction A C D E F (underlying A C E Q)) ⟶
      of A D E (Bimodule.rightRestriction A C D E F (underlying A C E Q')) :=
  ⟨fun e => (moduleRestriction A D C F.op).map (g.val e),
    middleRightRestrictionMap_naturality A C D E F g⟩

@[simp]
lemma middleRightRestrictionMap_value_eval {Q Q' : BimoduleCategory A C E} (g : Q ⟶ Q')
    (d : D) (e : E) :
    (valueEvaluation A D E d e).map (middleRightRestrictionMap A C D E F g) =
      (valueEvaluation A C E (F.obj d) e).map g :=
  middleRightRestrictionMap_component A C D E F g d e

def middleRightRestrictionFunctor : BimoduleCategory A C E ⥤ BimoduleCategory A D E where
  obj Q := of A D E (Bimodule.rightRestriction A C D E F (underlying A C E Q))
  map g := middleRightRestrictionMap A C D E F g
  map_id Q := by
    apply hom_ext
    intro e
    exact (moduleRestriction A D C F.op).map_id _
  map_comp g h := by
    apply hom_ext
    intro e
    exact (moduleRestriction A D C F.op).map_comp _ _

end Right
end SerrePositivity.DifferentialGraded.BimoduleCategory
end

end MiddleRestrictionMaps

/-! ## MiddleLeftRestrictionCoherence（旧 SerrePositivity/DifferentialGraded/Bimodule/MiddleLeftRestrictionCoherence.lean） -/

/-! # 左側の中間制限の恒等・合成自然同型

## 概要
左側の中間制限の恒等・合成自然同型。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section MiddleLeftRestrictionCoherence

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D]

/-- 恒等dg関手に沿う直接の左制限は、右加群ごとに恒等となる同型で元に戻る。 -/
def middleLeftRestrictionIdObjIso (P : BimoduleCategory A B D) :
    (middleLeftRestrictionFunctor A B D D (DGFunctor.id D)).obj P ≅ P :=
  isoOfValueFamily A B D
    (M := (middleLeftRestrictionFunctor A B D D (DGFunctor.id D)).obj P) (N := P)
    (fun d => Iso.refl ((evaluation A B D d).obj P)) (by
    intro b d d'
    change ((underlying A B D
      ((middleLeftRestrictionFunctor A B D D (DGFunctor.id D)).obj P)).leftAt b).map d d' ≫
      homPostcompose ((underlying A B D P).value b d)
        ((moduleEvaluation A B b).map
          (X := (evaluation A B D d').obj P) (Y := (evaluation A B D d').obj P) (𝟙 _)) =
      ((underlying A B D P).leftAt b).map d d' ≫
        homPrecompose ((moduleEvaluation A B b).map
          (X := (evaluation A B D d).obj P) (Y := (evaluation A B D d).obj P) (𝟙 _))
          ((underlying A B D P).value b d')
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    apply hom_naturality_of_apply
    intro p f
    refine (Cochain.comp_id _).trans ?_
    refine Eq.trans ?_ (Cochain.id_comp _).symm
    have hh :
        (Bimodule.leftAt (underlying A B D
          ((middleLeftRestrictionFunctor A B D D (DGFunctor.id D)).obj P)) b).map d d' =
          ((underlying A B D P).leftAt b).map d d' := by
      change ((𝟙 _ ≫ (underlying A B D P).map d d') ≫ moduleHomπ A B _ _ b) =
        (underlying A B D P).map d d' ≫ moduleHomπ A B _ _ b
      rw [Category.id_comp]
    exact congrArg (fun k => k.f p f) hh)

@[simp]
lemma middleLeftRestrictionIdObjIso_hom_eval (P : BimoduleCategory A B D) (d : D) :
    (evaluation A B D d).map (middleLeftRestrictionIdObjIso A B D P).hom = 𝟙 _ := rfl

/-- 直接の左制限の恒等比較は任意の閉零bimodule射に自然。 -/
def middleLeftRestrictionIdIso :
    middleLeftRestrictionFunctor A B D D (DGFunctor.id D) ≅ 𝟭 (BimoduleCategory A B D) :=
  NatIso.ofComponents (middleLeftRestrictionIdObjIso A B D) (by
    intro P P' f
    apply hom_ext
    intro d
    change f.val d ≫ 𝟙 _ = 𝟙 _ ≫ f.val d
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

variable (E : Type z) [DGCategory A E] (T : Type t) [DGCategory A T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 二段階の左制限と合成dg関手による左制限の、右加群ごとに恒等となる同型。 -/
def middleLeftRestrictionCompObjIso (P : BimoduleCategory A B T) :
    (middleLeftRestrictionFunctor A B E D F).obj
        ((middleLeftRestrictionFunctor A B T E G).obj P) ≅
      (middleLeftRestrictionFunctor A B T D (F.comp G)).obj P :=
  isoOfValueFamily A B D
    (M := (middleLeftRestrictionFunctor A B E D F).obj
      ((middleLeftRestrictionFunctor A B T E G).obj P))
    (N := (middleLeftRestrictionFunctor A B T D (F.comp G)).obj P)
    (fun d => Iso.refl ((evaluation A B T (G.obj (F.obj d))).obj P)) (by
    intro b d d'
    change ((underlying A B D ((middleLeftRestrictionFunctor A B E D F).obj
      ((middleLeftRestrictionFunctor A B T E G).obj P))).leftAt b).map d d' ≫
      homPostcompose ((underlying A B T P).value b (G.obj (F.obj d)))
        ((moduleEvaluation A B b).map
          (X := (evaluation A B T (G.obj (F.obj d'))).obj P)
          (Y := (evaluation A B T (G.obj (F.obj d'))).obj P) (𝟙 _)) =
      (Bimodule.leftAt (underlying A B D
        ((middleLeftRestrictionFunctor A B T D (F.comp G)).obj P)) b).map d d' ≫
        homPrecompose ((moduleEvaluation A B b).map
          (X := (evaluation A B T (G.obj (F.obj d))).obj P)
          (Y := (evaluation A B T (G.obj (F.obj d))).obj P) (𝟙 _))
          ((underlying A B T P).value b (G.obj (F.obj d')))
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    apply hom_naturality_of_apply
    intro p f
    refine (Cochain.comp_id _).trans ?_
    refine Eq.trans ?_ (Cochain.id_comp _).symm
    have hh :
        ((underlying A B D ((middleLeftRestrictionFunctor A B E D F).obj
          ((middleLeftRestrictionFunctor A B T E G).obj P))).leftAt b).map d d' =
        (Bimodule.leftAt (underlying A B D
          ((middleLeftRestrictionFunctor A B T D (F.comp G)).obj P)) b).map d d' := by
      change ((F.map d d' ≫ (G.map (F.obj d) (F.obj d') ≫
        (underlying A B T P).map (G.obj (F.obj d)) (G.obj (F.obj d')))) ≫
          moduleHomπ A B _ _ b) =
        (((F.map d d' ≫ G.map (F.obj d) (F.obj d')) ≫
          (underlying A B T P).map (G.obj (F.obj d)) (G.obj (F.obj d'))) ≫
            moduleHomπ A B _ _ b)
      simp only [Category.assoc]
    exact congrArg (fun k => k.f p f) hh)

@[simp]
lemma middleLeftRestrictionCompObjIso_hom_eval (P : BimoduleCategory A B T) (d : D) :
    (evaluation A B D d).map (middleLeftRestrictionCompObjIso A B D E T F G P).hom = 𝟙 _ := rfl

/-- 二段階の直接左制限の比較は任意の閉零bimodule射に自然。 -/
def middleLeftRestrictionCompIso :
    middleLeftRestrictionFunctor A B T E G ⋙ middleLeftRestrictionFunctor A B E D F ≅
      middleLeftRestrictionFunctor A B T D (F.comp G) :=
  NatIso.ofComponents (middleLeftRestrictionCompObjIso A B D E T F G) (by
    intro P P' f
    apply hom_ext
    intro d
    change f.val (G.obj (F.obj d)) ≫ 𝟙 _ = 𝟙 _ ≫ f.val (G.obj (F.obj d))
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

end SerrePositivity.DifferentialGraded.BimoduleCategory
end

end MiddleLeftRestrictionCoherence

/-! ## MiddleRightRestrictionCoherence（旧 SerrePositivity/DifferentialGraded/Bimodule/MiddleRightRestrictionCoherence.lean） -/

/-! # 右側の中間制限の恒等・合成自然同型

## 概要
右側の中間制限の恒等・合成自然同型。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section MiddleRightRestrictionCoherence

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (L : Type t) [DGCategory A L]

/-- 恒等右制限は、既存の右加群の恒等制限比較で元のbimoduleに戻る。 -/
def middleRightRestrictionIdObjIso (Q : BimoduleCategory A D L) :
    (middleRightRestrictionFunctor A D D L (DGFunctor.id D)).obj Q ≅ Q :=
  isoOfValueFamily A D L
    (M := (middleRightRestrictionFunctor A D D L (DGFunctor.id D)).obj Q) (N := Q)
    (fun l => moduleRestrictionIdObjIso A D ((evaluation A D L l).obj Q)) (by
      intro d l l'
      simp only [moduleRestrictionIdObjIso_hom_eval]
      apply hom_naturality_of_apply
      intro p f
      refine (Cochain.comp_id _).trans ?_
      refine Eq.trans ?_ (Cochain.id_comp _).symm
      exact congrArg (fun k => k.f p f)
        (Bimodule.rightRestriction_leftAt_map A D D L (DGFunctor.id D)
          (underlying A D L Q) d l l'))

@[simp]
lemma middleRightRestrictionIdObjIso_hom_value (Q : BimoduleCategory A D L) (d : D) (l : L) :
    (valueEvaluation A D L d l).map (middleRightRestrictionIdObjIso A D L Q).hom = 𝟙 _ :=
  moduleRestrictionIdObjIso_hom_eval A D ((evaluation A D L l).obj Q) d

def middleRightRestrictionIdIso :
    middleRightRestrictionFunctor A D D L (DGFunctor.id D) ≅ 𝟭 (BimoduleCategory A D L) :=
  NatIso.ofComponents (middleRightRestrictionIdObjIso A D L) (by
    intro Q Q' f
    apply hom_ext
    intro l
    exact (moduleRestrictionIdIso A D).hom.naturality (f.val l))

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : Type z) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 二段階の右制限と合成dg関手の右制限を、既存の加群制限比較で結ぶ。 -/
def middleRightRestrictionCompObjIso (Q : BimoduleCategory A T L) :
    (middleRightRestrictionFunctor A E D L F).obj
        ((middleRightRestrictionFunctor A T E L G).obj Q) ≅
      (middleRightRestrictionFunctor A T D L (F.comp G)).obj Q :=
  isoOfValueFamily A D L
    (M := (middleRightRestrictionFunctor A E D L F).obj
      ((middleRightRestrictionFunctor A T E L G).obj Q))
    (N := (middleRightRestrictionFunctor A T D L (F.comp G)).obj Q)
    (fun l => moduleRestrictionCompObjIso A D E T F.op G.op ((evaluation A T L l).obj Q)) (by
      intro d l l'
      simp only [moduleRestrictionCompObjIso_hom_eval]
      apply hom_naturality_of_apply
      intro p f
      refine (Cochain.comp_id _).trans ?_
      refine Eq.trans ?_ (Cochain.id_comp _).symm
      have h₁ := Bimodule.rightRestriction_leftAt_map A E D L F
        (Bimodule.rightRestriction A T E L G (underlying A T L Q)) d l l'
      have h₂ := Bimodule.rightRestriction_leftAt_map A T E L G
        (underlying A T L Q) (F.obj d) l l'
      have h₃ := Bimodule.rightRestriction_leftAt_map A T D L (F.comp G)
        (underlying A T L Q) d l l'
      exact congrArg (fun k => k.f p f) (h₁.trans (h₂.trans h₃.symm)))

@[simp]
lemma middleRightRestrictionCompObjIso_hom_value (Q : BimoduleCategory A T L) (d : D) (l : L) :
    (valueEvaluation A D L d l).map
        (middleRightRestrictionCompObjIso A D L E T F G Q).hom = 𝟙 _ :=
  moduleRestrictionCompObjIso_hom_eval A D E T F.op G.op ((evaluation A T L l).obj Q) d

def middleRightRestrictionCompIso :
    middleRightRestrictionFunctor A T E L G ⋙ middleRightRestrictionFunctor A E D L F ≅
      middleRightRestrictionFunctor A T D L (F.comp G) :=
  NatIso.ofComponents (middleRightRestrictionCompObjIso A D L E T F G) (by
    intro Q Q' f
    apply hom_ext
    intro l
    exact (moduleRestrictionCompIso A D E T F.op G.op).hom.naturality (f.val l))

end SerrePositivity.DifferentialGraded.BimoduleCategory
end

end MiddleRightRestrictionCoherence

/-! ## IdentityTranspose（旧 SerrePositivity/DifferentialGraded/Bimodule/IdentityTranspose.lean） -/

/-! # 対角bimoduleの転置作用の成分 -/

@[expose] public section IdentityTranspose

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma diagonal_transpose_element {b b' : Dᵒᵖ} (x : D) {p s n : ℤ}
    (f : GradedHom A b b' p) (h : GradedHom A b.unop x s) (hn : s + p = n) :
    (((leftModuleHomπ A D ((diagonal A D).leftAt b.unop)
      ((diagonal A D).leftAt b'.unop) x).f p
        (((diagonal A D).transposeHom b b').f p f)).v s n hn) h =
    forward A (D := D) (x := b'.unop) (y := b.unop) (z := x) f h (by omega) := by
  have hp := congrArg (fun t => t.f p f) ((diagonal A D).transposeHom_π b b' x)
  change (leftModuleHomπ A D ((diagonal A D).leftAt b.unop)
      ((diagonal A D).leftAt b'.unop) x).f p
        (((diagonal A D).transposeHom b b').f p f) =
    ((representable A x).map b b').f p f at hp
  rw [hp]
  exact representableMap_apply A x b b' p s n hn f h

end SerrePositivity.DifferentialGraded.Bimodule
end

end IdentityTranspose

/-! ## ParameterEvaluation（旧 SerrePositivity/DifferentialGraded/Bimodule/ParameterEvaluation.lean） -/

/-! # 任意パラメータのbimodule変換の両対象評価 -/

@[expose] public section ParameterEvaluation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]
variable {K : Complex A} {M N : Bimodule A B C}

/-- パラメータ付き変換を両対象で評価するchain map。 -/
def paramValue (τ : BimoduleParamTrans A B C K M N) (b : B) (c : C) :
    K ⟶ homComplex A (M.value b c) (N.value b c) :=
  τ.app c ≫ moduleHomπ A B (M.rightAt c) (N.rightAt c) b

/-- 左対象を固定すると全次数自然な右B加群変換になる。 -/
def paramRightAt (τ : BimoduleParamTrans A B C K M N) (c : C) :
    ModuleParamTrans A B K (M.rightAt c) (N.rightAt c) :=
  moduleHomEquiv A B K (M.rightAt c) (N.rightAt c) (τ.app c)

@[simp]
lemma paramRightAt_app (τ : BimoduleParamTrans A B C K M N) (b : B) (c : C) :
    (paramRightAt A B C τ c).app (op b) = paramValue A B C τ b c := rfl

lemma paramValue_right_naturality (τ : BimoduleParamTrans A B C K M N)
    (c : C) (b b' : Bᵒᵖ) :
    (β_ K (b ⟶[Complex A] b')).hom ≫
      ((M.rightAt c).map b b' ⊗ₘ paramValue A B C τ b'.unop c) ≫
        enrichedComposition _ _ _ =
    (paramValue A B C τ b.unop c ⊗ₘ (N.rightAt c).map b b') ≫
      enrichedComposition _ _ _ :=
  (paramRightAt A B C τ c).naturality b b'

/-- Hom endの合成を評価すると、左C作用に関する全Hom自然性が得られる。 -/
lemma paramValue_left_naturality (τ : BimoduleParamTrans A B C K M N)
    (b : B) (c c' : C) :
    (β_ K (c ⟶[Complex A] c')).hom ≫
      ((M.leftAt b).map c c' ⊗ₘ paramValue A B C τ b c') ≫ enrichedComposition _ _ _ =
    (paramValue A B C τ b c ⊗ₘ (N.leftAt b).map c c') ≫ enrichedComposition _ _ _ := by
  have h := congrArg (fun f => f ≫
    moduleHomπ A B (M.rightAt c) (N.rightAt c') b) (τ.naturality c c')
  change (β_ K (c ⟶[Complex A] c')).hom ≫
      (M.toFunctor.map c c' ⊗ₘ τ.app c') ≫
        moduleComposition A B (M.rightAt c) (M.rightAt c') (N.rightAt c') ≫
          moduleHomπ A B (M.rightAt c) (N.rightAt c') b =
    (τ.app c ⊗ₘ N.toFunctor.map c c') ≫
      moduleComposition A B (M.rightAt c) (N.rightAt c) (N.rightAt c') ≫
        moduleHomπ A B (M.rightAt c) (N.rightAt c') b at h
  rw [moduleComposition_π, moduleComposition_π] at h
  simp only [tensorHom_comp_tensorHom_assoc] at h
  exact h

/-- 右対象を固定した全次数自然な左C加群変換。Cのsmall性は不要。 -/
def paramLeftAt (τ : BimoduleParamTrans A B C K M N) (b : B) :
    GradedNatTrans ((Center.ofBraided (Complex A)).obj K)
      (M.leftAt b) (N.leftAt b) where
  app c := paramValue A B C τ b c
  naturality := paramValue_left_naturality A B C τ b

@[simp]
lemma paramLeftAt_app (τ : BimoduleParamTrans A B C K M N) (b : B) (c : C) :
    (paramLeftAt A B C τ b).app c = paramValue A B C τ b c := rfl

/-- パラメータ付きbimodule変換の等式を全ての値で判定する。 -/
lemma paramValue_ext {τ υ : BimoduleParamTrans A B C K M N}
    (h : ∀ b c, paramValue A B C τ b c = paramValue A B C υ b c) : τ = υ := by
  apply GradedNatTrans.ext
  funext c
  apply moduleHom_ext
  intro b
  exact h b c

end SerrePositivity.DifferentialGraded.Bimodule
end

end ParameterEvaluation

/-! ## ParameterSquare（旧 SerrePositivity/DifferentialGraded/Bimodule/ParameterSquare.lean） -/

/-! # パラメータ付き変換の可換式を値から主Hom endへ戻す -/

@[expose] public section ParameterSquare

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

lemma param_square_of_values {K : Complex A} {M M' N N' : Bimodule A B C}
    (τ : BimoduleParamTrans A B C K M M') (υ : BimoduleParamTrans A B C K N N')
    (a : ∀ c, ForgetEnrichment.of (Complex A) (M.rightAt c) ⟶
      ForgetEnrichment.of (Complex A) (N.rightAt c))
    (a' : ∀ c, ForgetEnrichment.of (Complex A) (M'.rightAt c) ⟶
      ForgetEnrichment.of (Complex A) (N'.rightAt c))
    (h : ∀ b c, paramValue A B C τ b c ≫
      homPostcompose (M.value b c) (moduleMorphismComponent A B _ _ (a' c) b) =
      paramValue A B C υ b c ≫
        homPrecompose (moduleMorphismComponent A B _ _ (a c) b) (N'.value b c)) (c : C) :
    τ.app c ≫ moduleHomPostcompose A B (M.rightAt c) (M'.rightAt c) (N'.rightAt c) (a' c) =
    υ.app c ≫ moduleHomPrecompose A B (M.rightAt c) (N.rightAt c) (N'.rightAt c) (a c) := by
  apply moduleHom_ext
  intro b
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  exact h b c

end SerrePositivity.DifferentialGraded.Bimodule
end

end ParameterSquare

/-! ## ParameterFamily（旧 SerrePositivity/DifferentialGraded/Bimodule/ParameterFamily.lean） -/

/-! # 全Hom自然なパラメータ付き右加群変換族からのbimodule変換 -/

@[expose] public section ParameterFamily

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 左加群の斉次cochainの符号付き交換式から全Hom自然性を復元する。 -/
lemma leftParamNaturality_of_cochain {C : Type w} [DGCategory A C]
    {K : Complex A} {M N : LeftModule A C}
    (a : ∀ c, K ⟶ homComplex A (M.obj c) (N.obj c))
    (h : ∀ (c c' : C) (k p m : ℤ) (hm : k + p = m)
      (t : K.X k) (f : GradedHom A c c' p),
      ((M.map c c').f p f).comp ((a c').f k t) (by omega) =
        (k * p).negOnePow • (((a c).f k t).comp ((N.map c c').f p f) hm)) (c c' : C) :
    (β_ K (c ⟶[Complex A] c')).hom ≫
      (M.map c c' ⊗ₘ a c') ≫ enrichedComposition _ _ _ =
    (a c ⊗ₘ N.map c c') ≫ enrichedComposition _ _ _ := by
  have hh := moduleParamNaturality_of_cochain A
    (M := M.toRightOpposite) (N := N.toRightOpposite) (fun x => a x.unop.unop)
    (fun x y k p m hm t f => by
      change (((𝟙 _ ≫ M.map x.unop.unop y.unop.unop).f p f).comp
          ((a y.unop.unop).f k t) (by omega)) =
        (k * p).negOnePow • (((a x.unop.unop).f k t).comp
          ((𝟙 _ ≫ N.map x.unop.unop y.unop.unop).f p f) hm)
      simpa only [Category.id_comp] using h x.unop.unop y.unop.unop k p m hm t f)
    (op (op c)) (op (op c'))
  change (β_ K (c ⟶[Complex A] c')).hom ≫
      ((𝟙 _ ≫ M.map c c') ⊗ₘ a c') ≫ enrichedComposition _ _ _ =
    (a c ⊗ₘ (𝟙 _ ≫ N.map c c')) ≫ enrichedComposition _ _ _ at hh
  simpa only [Category.id_comp] using hh

variable (B : Type v) (C : Type w) [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 左右の全Hom自然性を保持する変換族を主bimodule変換へ束ねる。 -/
def paramFamilyTrans {K : Complex A} {M N : Bimodule A B C}
    (a : ∀ c, ModuleParamTrans A B K (M.rightAt c) (N.rightAt c))
    (h : ∀ (b : B) (c c' : C), (β_ K (c ⟶[Complex A] c')).hom ≫
      ((M.leftAt b).map c c' ⊗ₘ (a c').app (op b)) ≫ enrichedComposition _ _ _ =
      ((a c).app (op b) ⊗ₘ (N.leftAt b).map c c') ≫ enrichedComposition _ _ _) :
    BimoduleParamTrans A B C K M N where
  app c := (moduleHomEquiv A B K (M.rightAt c) (N.rightAt c)).symm (a c)
  naturality c c' := by
    apply moduleHom_ext
    intro b
    change (β_ K (c ⟶[Complex A] c')).hom ≫
        (M.toFunctor.map c c' ⊗ₘ (moduleHomEquiv A B K _ _).symm (a c')) ≫
          moduleComposition A B (M.rightAt c) (M.rightAt c') (N.rightAt c') ≫
            moduleHomπ A B (M.rightAt c) (N.rightAt c') b =
      ((moduleHomEquiv A B K _ _).symm (a c) ⊗ₘ N.toFunctor.map c c') ≫
        moduleComposition A B (M.rightAt c) (N.rightAt c) (N.rightAt c') ≫
          moduleHomπ A B (M.rightAt c) (N.rightAt c') b
    rw [moduleComposition_π, moduleComposition_π]
    simp only [tensorHom_comp_tensorHom_assoc, moduleHomEquiv_symm_π]
    exact h b c c'

@[simp]
lemma paramFamilyTrans_value {K : Complex A} {M N : Bimodule A B C} (a h) (b : B) (c : C) :
    paramValue A B C (paramFamilyTrans A B C (K := K) (M := M) (N := N) a h) b c =
      (a c).app (op b) := moduleHomEquiv_symm_π A B K _ _ (a c) b

end SerrePositivity.DifferentialGraded.Bimodule
end

end ParameterFamily

/-! ## RightRestrictionLeftEvaluation（旧 SerrePositivity/DifferentialGraded/Bimodule/RightRestrictionLeftEvaluation.lean） -/

/-! # 右作用制限後の左加群評価を元の評価へ比較する

## 概要
右作用制限後の左加群評価を元の評価へ比較する。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RightRestrictionLeftEvaluation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] (F : DGFunctor A D B)

/-- 右作用を制限したbimoduleの左加群は、元の左加群の対象を再選択したものである。 -/
lemma rightRestriction_leftAt_eq (P : Bimodule A B C) (d : D) :
    (rightRestriction A B D C F P).leftAt d = P.leftAt (F.obj d) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := (rightRestriction A B D C F P).leftAt d) (G := P.leftAt (F.obj d)) (fun _ => rfl)
  intro c c'
  simp only [eqToHom_refl, Category.comp_id]
  exact rightRestriction_leftAt_map A B D C F P d c c'

variable [Small.{u} C]

/-- 閉零左加群圏上の、制限後評価と元の評価の同型。 -/
def rightRestrictionLeftEvaluationIso (P : BimoduleCategory A B C) (d : D) :
    (BimoduleCategory.leftEvaluation A D C d).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).obj P) ≅
      (BimoduleCategory.leftEvaluation A B C (F.obj d)).obj P :=
  eqToIso (rightRestriction_leftAt_eq A B D C F _ d)

@[simp]
lemma rightRestrictionLeftEvaluationIso_hom_eval (P : BimoduleCategory A B C) (d : D) (c : C) :
    (leftModuleEvaluation A C c).map (rightRestrictionLeftEvaluationIso A B D C F P d).hom =
      𝟙 _ := by
  simp only [rightRestrictionLeftEvaluationIso, eqToIso.hom, eqToHom_map]
  rfl

@[simp]
lemma rightRestrictionLeftEvaluationIso_inv_eval (P : BimoduleCategory A B C) (d : D) (c : C) :
    (leftModuleEvaluation A C c).map (rightRestrictionLeftEvaluationIso A B D C F P d).inv =
      𝟙 _ := by
  simp only [rightRestrictionLeftEvaluationIso, eqToIso.inv, eqToHom_map]
  rfl

end SerrePositivity.DifferentialGraded.Bimodule
end

end RightRestrictionLeftEvaluation

/-! ## ResolvedRestrictionAugmentation（旧 SerrePositivity/DifferentialGraded/Bimodule/ResolvedRestrictionAugmentation.lean） -/

/-! # 二段階の制限後bimoduleモデルの増大を合成する

## 概要
二段階の制限後bimoduleモデルの増大を合成する。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section ResolvedRestrictionAugmentation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : Type z) [DGCategory A T] [Small.{u} T]
  (L : Type t) [DGCategory A L]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 二段目の増大をさらに制限し、合成制限の表示へ送る射。 -/
def middleRightRestrictionCompositeMap
    {R : BimoduleCategory A E L} {Q : BimoduleCategory A T L}
    (q : R ⟶ (middleRightRestrictionFunctor A T E L G).obj Q) :
    (middleRightRestrictionFunctor A E D L F).obj R ⟶
      (middleRightRestrictionFunctor A T D L (F.comp G)).obj Q :=
  (middleRightRestrictionFunctor A E D L F).map q ≫
    (middleRightRestrictionCompObjIso A D L E T F G Q).hom

@[simp]
lemma middleRightRestrictionCompositeMap_value
    {R : BimoduleCategory A E L} {Q : BimoduleCategory A T L}
    (q : R ⟶ (middleRightRestrictionFunctor A T E L G).obj Q) (d : D) (l : L) :
    (valueEvaluation A D L d l).map (middleRightRestrictionCompositeMap A D E T L F G q) =
      (valueEvaluation A E L (F.obj d) l).map q := by
  simp only [middleRightRestrictionCompositeMap, CategoryTheory.Functor.map_comp,
    middleRightRestrictionCompObjIso_hom_value, Category.comp_id]
  exact middleRightRestrictionMap_value_eval A E D L F q d l

lemma middleRightRestrictionCompositeMap_quasiIso
    {R : BimoduleCategory A E L} {Q : BimoduleCategory A T L}
    (q : R ⟶ (middleRightRestrictionFunctor A T E L G).obj Q) (hq : quasiIso A E L q) :
    quasiIso A D L (middleRightRestrictionCompositeMap A D E T L F G q) := by
  intro d l
  rw [middleRightRestrictionCompositeMap_value]
  exact hq (F.obj d) l

/-- 二つの増大を、合成関手の右制限への増大へまとめる。 -/
def resolvedRestrictionAugmentationComp
    {S : BimoduleCategory A D L} {R : BimoduleCategory A E L} {Q : BimoduleCategory A T L}
    (r : S ⟶ (middleRightRestrictionFunctor A E D L F).obj R)
    (q : R ⟶ (middleRightRestrictionFunctor A T E L G).obj Q) :
    S ⟶ (middleRightRestrictionFunctor A T D L (F.comp G)).obj Q :=
  r ≫ (middleRightRestrictionFunctor A E D L F).map q ≫
    (middleRightRestrictionCompObjIso A D L E T F G Q).hom

@[simp]
lemma resolvedRestrictionAugmentationComp_value
    {S : BimoduleCategory A D L} {R : BimoduleCategory A E L} {Q : BimoduleCategory A T L}
    (r : S ⟶ (middleRightRestrictionFunctor A E D L F).obj R)
    (q : R ⟶ (middleRightRestrictionFunctor A T E L G).obj Q) (d : D) (l : L) :
    (valueEvaluation A D L d l).map (resolvedRestrictionAugmentationComp A D E T L F G r q) =
      (valueEvaluation A D L d l).map r ≫ (valueEvaluation A E L (F.obj d) l).map q := by
  simp only [resolvedRestrictionAugmentationComp, CategoryTheory.Functor.map_comp,
    middleRightRestrictionCompObjIso_hom_value, Category.comp_id]
  exact congrArg (fun k => (valueEvaluation A D L d l).map r ≫ k)
    (middleRightRestrictionMap_value_eval A E D L F q d l)

lemma resolvedRestrictionAugmentationComp_quasiIso
    {S : BimoduleCategory A D L} {R : BimoduleCategory A E L} {Q : BimoduleCategory A T L}
    (r : S ⟶ (middleRightRestrictionFunctor A E D L F).obj R)
    (q : R ⟶ (middleRightRestrictionFunctor A T E L G).obj Q)
    (hr : quasiIso A D L r) (hq : quasiIso A E L q) :
    quasiIso A D L (resolvedRestrictionAugmentationComp A D E T L F G r q) := by
  intro d l
  rw [resolvedRestrictionAugmentationComp_value]
  have : QuasiIso ((valueEvaluation A D L d l).map r) := hr d l
  have : QuasiIso ((valueEvaluation A E L (F.obj d) l).map q) := hq (F.obj d) l
  exact quasiIso_comp _ _

/-- 恒等右制限への指定増大を、元のbimoduleへの射として読む。 -/
def resolvedRestrictionAugmentationId {S Q : BimoduleCategory A D L}
    (q : S ⟶ (middleRightRestrictionFunctor A D D L (DGFunctor.id D)).obj Q) : S ⟶ Q :=
  q ≫ (middleRightRestrictionIdObjIso A D L Q).hom

@[simp]
lemma resolvedRestrictionAugmentationId_value {S Q : BimoduleCategory A D L}
    (q : S ⟶ (middleRightRestrictionFunctor A D D L (DGFunctor.id D)).obj Q) (d : D) (l : L) :
    (valueEvaluation A D L d l).map (resolvedRestrictionAugmentationId A D L q) =
      (valueEvaluation A D L d l).map q := by
  rw [resolvedRestrictionAugmentationId, CategoryTheory.Functor.map_comp,
    middleRightRestrictionIdObjIso_hom_value, Category.comp_id]

lemma resolvedRestrictionAugmentationId_quasiIso {S Q : BimoduleCategory A D L}
    (q : S ⟶ (middleRightRestrictionFunctor A D D L (DGFunctor.id D)).obj Q)
    (hq : quasiIso A D L q) : quasiIso A D L (resolvedRestrictionAugmentationId A D L q) := by
  intro d l
  rw [resolvedRestrictionAugmentationId_value]
  exact hq d l

end SerrePositivity.DifferentialGraded.BimoduleCategory
end

end ResolvedRestrictionAugmentation
