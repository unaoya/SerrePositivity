module

public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.CategoriesAndModules
public import SerrePositivity.DifferentialGraded.Tensor.Parameter
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.KFlatness
public import SerrePositivity.DifferentialGraded.Module.RestrictionRepresentable
public import SerrePositivity.DifferentialGraded.Tensor.LeftUnitRestriction
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionKFlatUnit
public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements
public import SerrePositivity.DifferentialGraded.Module.RestrictionCoherence

/-!
# Tensor.ResolvedRestriction

## 概要
4 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## RestrictionComparisonYoneda（旧 SerrePositivity/DifferentialGraded/Tensor/RestrictionComparisonYoneda.lean） -/

/-! # 制限tensor比較と代表加群のYoneda評価

## 概要
Hom準同型性と制限後の左相対K-flat性の下で、像の代表加群における比較を検証する。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictionComparisonYoneda
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- Hom写像による代表加群比較を制限された左因子とtensorする。 -/
def representableRestrictionTensorMap (d : D) (N : LeftModule A E) :
    obj A D (representable A d) (F.comp N) ⟶
      obj A D (restrictModule A D E F.op (representable A (F.obj d))) (F.comp N) :=
  (rightTensorFunctor A D (F.comp N)).map (representableRestrictionMap A D E F d)

@[reassoc (attr := simp)]
lemma ι_representableRestrictionTensorMap (d x : D) (N : LeftModule A E) :
    ι A D (representable A d) (F.comp N) x ≫
        representableRestrictionTensorMap A D E F d N =
      (F.map x d ⊗ₘ 𝟙 (N.obj (F.obj x))) ≫
        ι A D (restrictModule A D E F.op (representable A (F.obj d))) (F.comp N) x := by
  have h := ι_map A D (representableRestrictionMap A D E F d)
    (𝟙 (ForgetEnrichment.of (Complex A) (F.comp N))) x
  rw [representableRestrictionMap_eval, CategoryTheory.Functor.map_id] at h
  exact h

/-- 比較と代表加群のHom写像を合わせると、元のYoneda評価そのものになる。 -/
lemma representableRestrictionTensorMap_comparison_yoneda (d : D) (N : LeftModule A E) :
    representableRestrictionTensorMap A D E F d N ≫
        restrictionComparison A D E F (representable A (F.obj d)) N ≫
          yonedaEvaluation A E (F.obj d) N = yonedaEvaluation A D d (F.comp N) := by
  apply hom_ext
  intro x
  rw [ι_representableRestrictionTensorMap_assoc, ι_restrictionComparison_assoc,
    ι_yonedaEvaluation, ι_yonedaEvaluation]
  exact (leftAction_restrict A D E F N x d).symm

lemma representableRestrictionTensorMap_quasiIso (hF : HomQuasiIso F) (d : D)
    (N : LeftModule A E) (hN : leftModuleRelativeKFlat A D (F.comp N)) :
    QuasiIso (representableRestrictionTensorMap A D E F d N) :=
  leftModuleRelativeKFlat_preserves_rightQuasiIso A D (F.comp N) hN
    (representableRestrictionMap A D E F d) (representableRestrictionMap_quasiIso A D E F hF d)

/-- 像の代表加群における実際の比較chain mapの準同型性。 -/
lemma restrictionComparison_representable_quasiIso (hF : HomQuasiIso F) (d : D)
    (N : LeftModule A E) (hN : leftModuleRelativeKFlat A D (F.comp N)) :
    QuasiIso (restrictionComparison A D E F (representable A (F.obj d)) N) := by
  have : QuasiIso (representableRestrictionTensorMap A D E F d N) :=
    representableRestrictionTensorMap_quasiIso A D E F hF d N hN
  have : IsIso (yonedaEvaluation A E (F.obj d) N) := (yonedaIso A E (F.obj d) N).isIso_hom
  have : IsIso (yonedaEvaluation A D d (F.comp N)) := (yonedaIso A D d (F.comp N)).isIso_hom
  have : QuasiIso (representableRestrictionTensorMap A D E F d N ≫
      restrictionComparison A D E F (representable A (F.obj d)) N ≫
        yonedaEvaluation A E (F.obj d) N) := by
    rw [representableRestrictionTensorMap_comparison_yoneda]
    infer_instance
  have : QuasiIso (restrictionComparison A D E F (representable A (F.obj d)) N ≫
      yonedaEvaluation A E (F.obj d) N) :=
    quasiIso_of_comp_left (representableRestrictionTensorMap A D E F d N) _
  exact quasiIso_of_comp_right _ (yonedaEvaluation A E (F.obj d) N)

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end RestrictionComparisonYoneda

/-! ## FunctorRestrictionQuasiIso（旧 SerrePositivity/DifferentialGraded/Tensor/FunctorRestrictionQuasiIso.lean） -/

/-! # 制限後の右K-flatモデルによる中間tensor比較の準同型性

## 概要
制限後の右K-flatモデルによる中間tensor比較の準同型性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorRestrictionQuasiIso
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 制限後の指定右加群モデルから、元の二因子のtensorへの実際の比較。 -/
def resolvedRestrictionComparison {R : ModuleCategory A D} {M : ModuleCategory A E}
    (q : R ⟶ (moduleRestriction A D E F.op).obj M) (N : LeftModule A E) :
    obj A D (ForgetEnrichment.to (Complex A) R) (F.comp N) ⟶
      obj A E (ForgetEnrichment.to (Complex A) M) N :=
  (rightTensorFunctor A D (F.comp N)).map q ≫
    restrictionComparison A D E F (ForgetEnrichment.to (Complex A) M) N

@[reassoc]
lemma ι_resolvedRestrictionComparison {R : ModuleCategory A D} {M : ModuleCategory A E}
    (q : R ⟶ (moduleRestriction A D E F.op).obj M) (N : LeftModule A E) (d : D) :
    ι A D (ForgetEnrichment.to (Complex A) R) (F.comp N) d ≫
        resolvedRestrictionComparison A D E F q N =
      ((moduleEvaluation A D d).map q ⊗ₘ 𝟙 (N.obj (F.obj d))) ≫
        ι A E (ForgetEnrichment.to (Complex A) M) N (F.obj d) := by
  have hm := ι_map A D q (𝟙 (ForgetEnrichment.of (Complex A) (F.comp N))) d
  simp only [CategoryTheory.Functor.map_id] at hm
  change _ ≫ _ ≫ restrictionComparison A D E F _ N = _
  refine (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ restrictionComparison A D E F
      (ForgetEnrichment.to (Complex A) M) N) hm).trans ?_)
  change (_ ⊗ₘ _) ≫ ι A D (restrictModule A D E F.op
    (ForgetEnrichment.to (Complex A) M)) (F.comp N) d ≫
      restrictionComparison A D E F (ForgetEnrichment.to (Complex A) M) N = _
  rw [ι_restrictionComparison]
  rfl

@[reassoc]
lemma ι_functorExtensionTranspose_eval {R : ModuleCategory A D} {M : ModuleCategory A E}
    (q : R ⟶ (moduleRestriction A D E F.op).obj M) (e : E) (d : D) :
    ι A D (ForgetEnrichment.to (Complex A) R) ((functorGraph A D E F).leftAt e) d ≫
        (moduleEvaluation A E e).map (functorExtensionTranspose A D E F q) =
      ((moduleEvaluation A D d).map q ⊗ₘ 𝟙 (homObject A E e (F.obj d))) ≫
        rightAction A E (ForgetEnrichment.to (Complex A) M) e (F.obj d) := by
  rw [functorExtensionTranspose_eq, CategoryTheory.Functor.map_comp,
    dgModuleExtension_map_eval, functorExtensionCounit_eval]
  have hm := ι_map A D q
    (𝟙 (ForgetEnrichment.of (Complex A) ((functorGraph A D E F).leftAt e))) d
  simp only [CategoryTheory.Functor.map_id] at hm
  refine (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ functorExtensionEvaluationComponent A D E F
      (ForgetEnrichment.to (Complex A) M) e) hm).trans ?_)
  change (_ ⊗ₘ _) ≫ ι A D (restrictModule A D E F.op
    (ForgetEnrichment.to (Complex A) M)) ((functorGraph A D E F).leftAt e) d ≫
      functorExtensionEvaluationComponent A D E F
        (ForgetEnrichment.to (Complex A) M) e = _
  rw [ι_functorExtensionEvaluationComponent]
  rfl

/-- balanced関係を、右因子への任意の複体射で前合成した形。 -/
lemma tensorAction_balance_map (T : Complex A) (M : RightModule A E) (N : LeftModule A E)
    (e e' : E) (f : T ⟶ M.obj (op e')) :
    (T ◁ leftAction A E N e e') ≫ (f ⊗ₘ 𝟙 (N.obj e')) ≫ ι A E M N e' =
      (α_ T (homObject A E e e') (N.obj e)).inv ≫
        (((f ⊗ₘ 𝟙 (homObject A E e e')) ≫ rightAction A E M e e') ▷ N.obj e) ≫
          ι A E M N e := by
  simp only [tensorHom_id, comp_whiskerRight, Category.assoc]
  rw [condition, ← associator_inv_naturality_left_assoc, Iso.inv_hom_id_assoc,
    whisker_exchange_assoc]

/-- 射影公式を通すと、実際の中間tensor比較は増大の随伴転置とのtensorになる。 -/
lemma functorExtensionTensorIso_resolvedComparison
    {R : ModuleCategory A D} {M : ModuleCategory A E}
    (q : R ⟶ (moduleRestriction A D E F.op).obj M) (N : LeftModule A E) :
    (functorExtensionTensorIso A D E F (ForgetEnrichment.to (Complex A) R) N).hom ≫
        resolvedRestrictionComparison A D E F q N =
      (rightTensorFunctor A E N).map (functorExtensionTranspose A D E F q) := by
  apply Fubini.right_hom_ext A E D (functorGraph A D E F)
    (ForgetEnrichment.to (Complex A) R) N
  intro e d
  rw [← Category.assoc, rightι_functorExtensionTensorIso_hom, Category.assoc,
    ι_resolvedRestrictionComparison]
  let T := (ForgetEnrichment.to (Complex A) R).obj (op d)
  let H := homObject A E e (F.obj d)
  let t := functorExtensionTranspose A D E F q
  have hb := tensorAction_balance_map A E T (ForgetEnrichment.to (Complex A) M) N
    e (F.obj d) ((moduleEvaluation A D d).map q)
  have he := ι_functorExtensionTranspose_eval A D E F q e d
  have hk := congrArg (fun k => (α_ T H (N.obj e)).inv ≫
    (k ▷ N.obj e) ≫ ι A E (ForgetEnrichment.to (Complex A) M) N e) he
  simp only [comp_whiskerRight, Category.assoc] at hk
  have hm := ι_map A E t (𝟙 (ForgetEnrichment.of (Complex A) N)) e
  simp only [CategoryTheory.Functor.map_id, tensorHom_id] at hm
  have hs := congrArg (fun k => (α_ T H (N.obj e)).inv ≫
    (ι A D (ForgetEnrichment.to (Complex A) R) ((functorGraph A D E F).leftAt e) d ▷
      N.obj e) ≫ k) hm
  simp only [comp_whiskerRight, Category.assoc] at hb
  simp only [tensorHom_id]
  change (T ◁ leftAction A E N e (F.obj d)) ≫
    ((moduleEvaluation A D d).map q ▷ N.obj (F.obj d)) ≫
      ι A E (ForgetEnrichment.to (Complex A) M) N (F.obj d) =
    (α_ T H (N.obj e)).inv ≫
      (ι A D (ForgetEnrichment.to (Complex A) R) ((functorGraph A D E F).leftAt e) d ▷
        N.obj e) ≫
      ι A E ((dgModuleExtension A D E F).obj (ForgetEnrichment.to (Complex A) R)) N e ≫
        map A E t (𝟙 (ForgetEnrichment.of (Complex A) N))
  exact hb.trans (hk.symm.trans hs.symm)

/-- 準同値と両端の右相対K-flat性から、制限後のモデルによる比較は準同型。 -/
lemma resolvedRestrictionComparison_quasiIso (hF : QuasiEquivalence F)
    {R : ModuleCategory A D} {M : ModuleCategory A E}
    (hR : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) R))
    (hM : moduleRelativeKFlat A E (ForgetEnrichment.to (Complex A) M))
    (q : R ⟶ (moduleRestriction A D E F.op).obj M) (hq : moduleQuasiIso A D q)
    (N : LeftModule A E) : QuasiIso (resolvedRestrictionComparison A D E F q N) := by
  have ht := functorExtensionTranspose_quasiIso A D E F hF hR q hq
  have he := functorExtension_relativeKFlat A D E F (ForgetEnrichment.to (Complex A) R) hR
  have htensor := rightTensor_relativeKFlat_quasiIso A E N he hM
    (functorExtensionTranspose A D E F q) ht
  have hc : QuasiIso
      ((functorExtensionTensorIso A D E F (ForgetEnrichment.to (Complex A) R) N).hom ≫
        resolvedRestrictionComparison A D E F q N) := by
    rw [functorExtensionTensorIso_resolvedComparison]
    exact htensor
  let := hc
  exact quasiIso_of_comp_left
    (functorExtensionTensorIso A D E F (ForgetEnrichment.to (Complex A) R) N).hom _

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end FunctorRestrictionQuasiIso

/-! ## ResolvedRestrictionCoherence（旧 SerrePositivity/DifferentialGraded/Tensor/ResolvedRestrictionCoherence.lean） -/

/-! # 制限後モデルを使うtensor比較の自己・推移整合性

## 概要
制限後モデルを使うtensor比較の自己・推移整合性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section ResolvedRestrictionCoherence
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : Type z) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 二段階の指定増大を、合成関手に沿う制限への一つの増大へ束ねる。 -/
def resolvedRestrictionAugmentationComp
    {S : ModuleCategory A D} {R : ModuleCategory A E} {M : ModuleCategory A T}
    (r : S ⟶ (moduleRestriction A D E F.op).obj R)
    (q : R ⟶ (moduleRestriction A E T G.op).obj M) :
    S ⟶ (moduleRestriction A D T (F.comp G).op).obj M :=
  r ≫ (moduleRestriction A D E F.op).map q ≫
    (moduleRestrictionCompObjIso A D E T F.op G.op M).hom

@[simp]
lemma resolvedRestrictionAugmentationComp_eval
    {S : ModuleCategory A D} {R : ModuleCategory A E} {M : ModuleCategory A T}
    (r : S ⟶ (moduleRestriction A D E F.op).obj R)
    (q : R ⟶ (moduleRestriction A E T G.op).obj M) (d : D) :
    (moduleEvaluation A D d).map (resolvedRestrictionAugmentationComp A D E T F G r q) =
      (moduleEvaluation A D d).map r ≫ (moduleEvaluation A E (F.obj d)).map q := by
  simp only [resolvedRestrictionAugmentationComp, CategoryTheory.Functor.map_comp,
    moduleRestrictionCompObjIso_hom_eval, moduleRestriction_map_eval, Category.comp_id]
  rfl

lemma resolvedRestrictionAugmentationComp_quasiIso
    {S : ModuleCategory A D} {R : ModuleCategory A E} {M : ModuleCategory A T}
    (r : S ⟶ (moduleRestriction A D E F.op).obj R)
    (q : R ⟶ (moduleRestriction A E T G.op).obj M)
    (hr : moduleQuasiIso A D r) (hq : moduleQuasiIso A E q) :
    moduleQuasiIso A D (resolvedRestrictionAugmentationComp A D E T F G r q) := by
  intro d
  rw [resolvedRestrictionAugmentationComp_eval]
  have : QuasiIso ((moduleEvaluation A D d).map r) := hr d
  have : QuasiIso ((moduleEvaluation A E (F.obj d)).map q) := hq (F.obj d)
  exact quasiIso_comp _ _

omit [Small.{u} D] [Small.{u} E] [Small.{u} T] in
lemma restrictionLeft_comp_assoc (N : LeftModule A T) :
    F.comp (G.comp N) = (F.comp G).comp N := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]

/-- 同じ制限後モデルを保ち、左作用の反復制限表示だけを替える同型。 -/
def resolvedRestrictionCompTensorIso (S : RightModule A D) (N : LeftModule A T) :
    obj A D S (F.comp (G.comp N)) ≅ obj A D S ((F.comp G).comp N) :=
  changeLeft A D S (restrictionLeft_comp_assoc A D E T F G N)

omit [Small.{u} E] [Small.{u} T] in
@[reassoc]
lemma ι_resolvedRestrictionCompTensorIso_hom (S : RightModule A D) (N : LeftModule A T) (d : D) :
    ι A D S (F.comp (G.comp N)) d ≫ (resolvedRestrictionCompTensorIso A D E T F G S N).hom =
      ι A D S ((F.comp G).comp N) d :=
  (ι_changeLeft_hom A D S (restrictionLeft_comp_assoc A D E T F G N) d).trans
    (Category.id_comp _)

/-- 指定モデルと増大を使う二段階の実際の比較は、合成関手による一段階の比較と一致。 -/
lemma resolvedRestrictionComparison_comp
    {S : ModuleCategory A D} {R : ModuleCategory A E} {M : ModuleCategory A T}
    (r : S ⟶ (moduleRestriction A D E F.op).obj R)
    (q : R ⟶ (moduleRestriction A E T G.op).obj M) (N : LeftModule A T) :
    (resolvedRestrictionCompTensorIso A D E T F G
      (ForgetEnrichment.to (Complex A) S) N).hom ≫
        resolvedRestrictionComparison A D T (F.comp G)
          (resolvedRestrictionAugmentationComp A D E T F G r q) N =
      resolvedRestrictionComparison A D E F r (G.comp N) ≫
        resolvedRestrictionComparison A E T G q N := by
  apply hom_ext A D (ForgetEnrichment.to (Complex A) S) (F.comp (G.comp N))
  intro d
  rw [ι_resolvedRestrictionCompTensorIso_hom_assoc, ι_resolvedRestrictionComparison,
    ι_resolvedRestrictionComparison_assoc, ι_resolvedRestrictionComparison,
    resolvedRestrictionAugmentationComp_eval]
  let rd : (ForgetEnrichment.to (Complex A) S).obj (op d) ⟶
      (ForgetEnrichment.to (Complex A) R).obj (op (F.obj d)) :=
    (moduleEvaluation A D d).map r
  let qd : (ForgetEnrichment.to (Complex A) R).obj (op (F.obj d)) ⟶
      (ForgetEnrichment.to (Complex A) M).obj (op (G.obj (F.obj d))) :=
    (moduleEvaluation A E (F.obj d)).map q
  change ((rd ≫ qd) ⊗ₘ 𝟙 (N.obj (G.obj (F.obj d)))) ≫
      ι A T (ForgetEnrichment.to (Complex A) M) N (G.obj (F.obj d)) =
    (rd ⊗ₘ 𝟙 (N.obj (G.obj (F.obj d)))) ≫
      (qd ⊗ₘ 𝟙 (N.obj (G.obj (F.obj d)))) ≫
        ι A T (ForgetEnrichment.to (Complex A) M) N (G.obj (F.obj d))
  rw [tensorHom_comp_tensorHom_assoc, Category.comp_id]

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end ResolvedRestrictionCoherence

/-! ## ResolvedRestrictionIdentity（旧 SerrePositivity/DifferentialGraded/Tensor/ResolvedRestrictionIdentity.lean） -/

/-! # 制限後の指定モデルによるtensor比較の恒等dg関手に関する整合性

## 概要
制限後の指定モデルによるtensor比較の恒等dg関手に関する整合性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section ResolvedRestrictionIdentity
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
lemma restrictionLeft_id (N : LeftModule A D) : (DGFunctor.id D).comp N = N := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]

/-- 恒等制限による左作用の表示を元に戻すtensor同型。 -/
def resolvedRestrictionIdTensorIso (S : RightModule A D) (N : LeftModule A D) :
    obj A D S ((DGFunctor.id D).comp N) ≅ obj A D S N :=
  changeLeft A D S (restrictionLeft_id A D N)

@[reassoc]
lemma ι_resolvedRestrictionIdTensorIso_hom (S : RightModule A D) (N : LeftModule A D) (d : D) :
    ι A D S ((DGFunctor.id D).comp N) d ≫ (resolvedRestrictionIdTensorIso A D S N).hom =
      ι A D S N d :=
  (ι_changeLeft_hom A D S (restrictionLeft_id A D N) d).trans (Category.id_comp _)

/-- 恒等制限への指定増大を元の右加群への射として読む。 -/
def resolvedRestrictionAugmentationId {S M : ModuleCategory A D}
    (q : S ⟶ (moduleRestriction A D D (DGFunctor.id Dᵒᵖ)).obj M) : S ⟶ M :=
  q ≫ (moduleRestrictionIdObjIso A D M).hom

@[simp]
lemma resolvedRestrictionAugmentationId_eval {S M : ModuleCategory A D}
    (q : S ⟶ (moduleRestriction A D D (DGFunctor.id Dᵒᵖ)).obj M) (d : D) :
    (moduleEvaluation A D d).map (resolvedRestrictionAugmentationId A D q) =
      (moduleEvaluation A D d).map q := by
  rw [resolvedRestrictionAugmentationId, CategoryTheory.Functor.map_comp,
    moduleRestrictionIdObjIso_hom_eval, Category.comp_id]

/-- 恒等dg関手の比較は、表示を戻して指定増大とtensorする写像そのもの。 -/
lemma resolvedRestrictionComparison_id {S M : ModuleCategory A D}
    (q : S ⟶ (moduleRestriction A D D (DGFunctor.id Dᵒᵖ)).obj M) (N : LeftModule A D) :
    resolvedRestrictionComparison A D D (DGFunctor.id D) q N =
      (resolvedRestrictionIdTensorIso A D (ForgetEnrichment.to (Complex A) S) N).hom ≫
        (rightTensorFunctor A D N).map (resolvedRestrictionAugmentationId A D q) := by
  apply hom_ext A D (ForgetEnrichment.to (Complex A) S) ((DGFunctor.id D).comp N)
  intro d
  rw [ι_resolvedRestrictionComparison, ι_resolvedRestrictionIdTensorIso_hom_assoc]
  have hmap := ι_map A D (resolvedRestrictionAugmentationId A D q)
    (𝟙 (ForgetEnrichment.of (Complex A) N)) d
  simp only [CategoryTheory.Functor.map_id, resolvedRestrictionAugmentationId_eval] at hmap
  exact hmap.symm

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end ResolvedRestrictionIdentity
