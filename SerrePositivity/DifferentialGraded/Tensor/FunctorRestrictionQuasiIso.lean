module
public import SerrePositivity.DifferentialGraded.Tensor.FunctorExtensionProjection
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionKFlatUnit
public import SerrePositivity.DifferentialGraded.Tensor.RestrictionComparison

/-! # 制限後の右K-flatモデルによる中間tensor比較の準同型性

## 概要
制限後の右K-flatモデルによる中間tensor比較の準同型性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
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
