module

public import SerrePositivity.DifferentialGraded.Tensor.BalancedElements
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import SerrePositivity.DifferentialGraded.Module.Cylinder
public import SerrePositivity.DifferentialGraded.Module.RestrictionTensor
public import SerrePositivity.DifferentialGraded.Bimodule.Right
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
public import SerrePositivity.DifferentialGraded.Derived.BimoduleBasic
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Components
public import SerrePositivity.DifferentialGraded.Tensor.Triple
public import SerrePositivity.DifferentialGraded.Bimodule.Value
public import SerrePositivity.DifferentialGraded.Complexes.HomMapEvaluation
public import SerrePositivity.DifferentialGraded.Module.Isomorphism

/-!
# Tensor.Compose

## 概要
10 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## TensorModuleNaturality（旧 SerrePositivity/DifferentialGraded/Tensor/TensorModuleNaturality.lean） -/

/-! # balanced tensorの外へ出す同型の生成複体に関する自然性とcylinder射影

## 概要
balanced tensorの外へ出す同型の生成複体に関する自然性とcylinder射影。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section TensorModuleNaturality
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma tensorModuleHom_naturality {K L : Complex A} (f : K ⟶ L)
    (M : RightModule A D) (N : LeftModule A D) :
    (rightTensorFunctor A D N).map (tensorModuleMap f M) ≫ tensorModuleHom A D L M N =
      tensorModuleHom A D K M N ≫ (f ⊗ₘ 𝟙 (obj A D M N)) := by
  apply hom_ext
  intro x
  have h := ι_map A D (tensorModuleMap f M) (𝟙 (ForgetEnrichment.of (Complex A) N)) x
  rw [tensorModuleMap_eval, CategoryTheory.Functor.map_id] at h
  have hL := ι_tensorModuleHom A D L M N x
  have hK := ι_tensorModuleHom_assoc A D K M N x (f ⊗ₘ 𝟙 (obj A D M N))
  have hm : ((f ⊗ₘ 𝟙 (M.obj (Opposite.op x))) ⊗ₘ 𝟙 (N.obj x)) ≫
      (α_ L (M.obj (Opposite.op x)) (N.obj x)).hom ≫ L ◁ ι A D M N x =
    (α_ K (M.obj (Opposite.op x)) (N.obj x)).hom ≫
      K ◁ ι A D M N x ≫ (f ⊗ₘ 𝟙 (obj A D M N)) := by
    simp only [tensorHom_id]
    rw [associator_naturality_left_assoc, whisker_exchange]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ tensorModuleHom A D L M N) h).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => ((f ⊗ₘ 𝟙 (M.obj (Opposite.op x))) ⊗ₘ 𝟙 (N.obj x)) ≫ k) hL).trans
          (hm.trans hK.symm))))

/-- interval射影は任意の固定左因子とのbalanced tensor後も準同型。 -/
lemma rightTensor_intervalProjection_quasiIso (M : RightModule A D) (N : LeftModule A D) :
    QuasiIso ((rightTensorFunctor A D N).map
      (tensorModuleMap (cylinder.π (𝟙_ (Complex A))) M)) := by
  have h := tensorModuleHom_naturality A D (cylinder.π (𝟙_ (Complex A))) M N
  have : IsIso (tensorModuleHom A D (dgInterval A) M N) :=
    (tensorModuleIso A D (dgInterval A) M N).isIso_hom
  have : IsIso (tensorModuleHom A D (𝟙_ (Complex A)) M N) :=
    (tensorModuleIso A D (𝟙_ (Complex A)) M N).isIso_hom
  have : QuasiIso (cylinder.π (𝟙_ (Complex A)) ⊗ₘ 𝟙 (obj A D M N)) :=
    (tensorIntervalHomotopyEquiv A (obj A D M N)).quasiIso_hom
  have : QuasiIso ((rightTensorFunctor A D N).map
      (tensorModuleMap (cylinder.π (𝟙_ (Complex A))) M) ≫
        tensorModuleHom A D (𝟙_ (Complex A)) M N) := h.symm ▸ (quasiIso_comp _ _)
  exact quasiIso_of_comp_right _ (tensorModuleHom A D (𝟙_ (Complex A)) M N)

lemma rightTensor_precylinderProjection_quasiIso (M : ModuleCategory A D)
    (N : LeftModule A D) :
    QuasiIso ((rightTensorFunctor A D N).map (modulePrecylinder A D M).π) := by
  have := rightTensor_intervalProjection_quasiIso A D (ForgetEnrichment.to (Complex A) M) N
  change QuasiIso ((rightTensorFunctor A D N).map
    (tensorModuleMap (cylinder.π (𝟙_ (Complex A))) (ForgetEnrichment.to (Complex A) M) ≫
      (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).hom))
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end TensorModuleNaturality

/-! ## RestrictionCylinder（旧 SerrePositivity/DifferentialGraded/Tensor/RestrictionCylinder.lean） -/

/-! # 制限された加群cylinder射影のbalanced tensor後の準同型性

## 概要
制限された加群cylinder射影のbalanced tensor後の準同型性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RestrictionCylinder
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A Dᵒᵖ Eᵒᵖ)

lemma moduleRestrictionTensorIso_hom_eval (K : Complex A) (M : ModuleCategory A E) (d : D) :
    (moduleEvaluation A D d).map (moduleRestrictionTensorIso A D E F K M).hom = 𝟙 _ := by
  simp only [moduleRestrictionTensorIso, eqToIso.hom, CategoryTheory.Functor.map_id,
    eqToHom_refl]

/-- 制限された標準cylinderの射影は、同じintervalを使った制限加群の射影と可換。 -/
lemma moduleRestriction_precylinderProjection (M : ModuleCategory A E) :
    (moduleRestriction A D E F).map (modulePrecylinder A E M).π =
      (moduleRestrictionTensorIso A D E F (dgInterval A) M).hom ≫
        (modulePrecylinder A D ((moduleRestriction A D E F).obj M)).π := by
  apply moduleMorphism_ext
  intro d
  rw [moduleRestriction_map_eval, CategoryTheory.Functor.map_comp,
    moduleRestrictionTensorIso_hom_eval]
  refine Eq.trans ?_ (Category.id_comp ((moduleEvaluation A D d).map
    (modulePrecylinder A D ((moduleRestriction A D E F).obj M)).π)).symm
  change (moduleEvaluation A E (F.obj (op d)).unop).map
      (tensorModuleMap (HomologicalComplex.cylinder.π (𝟙_ (Complex A)))
          (ForgetEnrichment.to (Complex A) M) ≫
        (moduleTensorUnitIso A E (ForgetEnrichment.to (Complex A) M)).hom) =
    (moduleEvaluation A D d).map
      (tensorModuleMap (HomologicalComplex.cylinder.π (𝟙_ (Complex A)))
          (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj M)) ≫
        (moduleTensorUnitIso A D
          (ForgetEnrichment.to (Complex A) ((moduleRestriction A D E F).obj M))).hom)
  simp only [CategoryTheory.Functor.map_comp, tensorModuleMap_eval, moduleTensorUnitIso_hom_eval]
  rfl

/-- 制限後の相対K-flat性を要求せず、cylinder射影のtensor像は準同型。 -/
lemma rightTensor_restrictedPrecylinderProjection_quasiIso (M : ModuleCategory A E)
    (N : LeftModule A D) :
    QuasiIso ((BalancedTensor.rightTensorFunctor A D N).map
      ((moduleRestriction A D E F).map (modulePrecylinder A E M).π)) := by
  have := BalancedTensor.rightTensor_precylinderProjection_quasiIso A D
    ((moduleRestriction A D E F).obj M) N
  rw [moduleRestriction_precylinderProjection, CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.DifferentialGraded
end

end RestrictionCylinder

/-! ## BimoduleCylinder（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleCylinder.lean） -/

/-! # 任意の前因子とのbimodule合成後のsource cylinder射影の準同型性

## 概要
任意の前因子とのbimodule合成後のsource cylinder射影の準同型性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCylinder
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]

/-- 前因子を固定した、既存の合成双関手の通常関手への制限。 -/
def composeAfter (P : BimoduleCategory A B C) :
    BimoduleCategory A C E ⥤ BimoduleCategory A B E :=
  (((Functor.const (BimoduleCategory A C E)).obj P).prod'
    (𝟭 (BimoduleCategory A C E))) ⋙ composeFunctor A B C E

lemma rightTensor_bimoduleSourcePrecylinderProjection_quasiIso
    (M : ModuleCategory A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ)
    (L : LeftModule A C) (e : E) :
    QuasiIso ((BalancedTensor.rightTensorFunctor A C L).map
      ((BimoduleCategory.evaluation A C E e).map
        ((rightModuleBimoduleEquivalence A C E).functor.map
          (modulePrecylinder A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ M).π))) := by
  let T := BalancedTensor.rightTensorFunctor A C L
  let J := rightModuleBimoduleRightRestrictionNatIso A C E e
  let π := (modulePrecylinder A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ M).π
  have h := congrArg (fun k => T.map k) (J.hom.naturality π)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
  have : QuasiIso (T.map ((tensorRightRestriction A C E e).map π)) :=
    rightTensor_restrictedPrecylinderProjection_quasiIso A C (DGTensorCategory A Cᵒᵖ E)ᵒᵖ
      (tensorRightRestrictionInclusion A C E e) M L
  have hM : IsIso (J.hom.app M) := (J.app M).isIso_hom
  have hI : IsIso (J.hom.app
      (modulePrecylinder A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ M).I) := (J.app _).isIso_hom
  have hTM : IsIso (T.map (J.hom.app M)) := T.map_isIso (J.hom.app M)
  have hTI : IsIso (T.map (J.hom.app
      (modulePrecylinder A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ M).I)) := T.map_isIso _
  have hr : QuasiIso (T.map (J.hom.app
      (modulePrecylinder A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ M).I) ≫
        T.map ((tensorRightRestriction A C E e).map π)) := quasiIso_comp _ _
  have hl : QuasiIso
      (T.map (((rightModuleBimoduleEquivalence A C E).functor ⋙
        BimoduleCategory.evaluation A C E e).map π) ≫ T.map (J.hom.app M)) := h.symm ▸ hr
  exact quasiIso_of_comp_right
    (T.map (((rightModuleBimoduleEquivalence A C E).functor ⋙
      BimoduleCategory.evaluation A C E e).map π)) (T.map (J.hom.app M))

/-- 任意の前因子でも、積dg圏上の標準cylinder射影は合成後に準同型。 -/
lemma composeAfter_sourcePrecylinderProjection_quasiIso (P : BimoduleCategory A B C)
    (M : ModuleCategory A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ) :
    BimoduleCategory.quasiIso A B E ((composeAfter A B C E P).map
      ((rightModuleBimoduleEquivalence A C E).functor.map
        (modulePrecylinder A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ M).π)) := by
  intro b e
  change QuasiIso ((BimoduleCategory.valueEvaluation A B E b e).map
    (composeMap A B C E (𝟙 P) ((rightModuleBimoduleEquivalence A C E).functor.map
      (modulePrecylinder A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ M).π)))
  rw [composeMap_value_eval]
  change QuasiIso (BalancedTensor.map A C
    ((BimoduleCategory.evaluation A C E e).map ((rightModuleBimoduleEquivalence A C E).functor.map
      (modulePrecylinder A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ M).π))
    ((BimoduleCategory.leftEvaluation A B C b).map (𝟙 P)))
  rw [CategoryTheory.Functor.map_id]
  exact rightTensor_bimoduleSourcePrecylinderProjection_quasiIso A C E M
    ((BimoduleCategory.underlying A B C P).leftAt b) e

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCylinder

/-! ## RightUnitAssociativity（旧 SerrePositivity/DifferentialGraded/Tensor/RightUnitAssociativity.lean） -/

/-!
概要：相対 tensor の右単位と結合同型の整合式を証明する。
方針：同じ三重斉次生成元で、結合後の Yoneda 評価と先に行う Yoneda 評価を比較する。
規約：元の実 tensor・結合・単位射を保持し、導来圏へ移さない。
使われ方：D-19 の代表加群上の実延長合成比較。
-/

@[expose] public section RightUnitAssociativity
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [Small.{u} B] [DGCategory A C] [Small.{u} C]
  [DGCategory A E] [Small.{u} E] (P : Bimodule A B C) (Q : Bimodule A C E)

lemma rightUnit_associator_value (b : B) (e : E) :
    (associatorValueIso A B C E E P Q (Bimodule.diagonal A E) b e).hom ≫
      composeValueMap A B C E (𝟙 (BimoduleCategory.of A B C P))
        (rightBimoduleUnitIso A C E Q).hom b e =
    (rightUnitValueIso A B E (compose A B C E P Q) b e).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply associatorLeft_degree_element_ext A B C E E P Q (Bimodule.diagonal A E) b e
  intro c e' k r s i hi hn t q v
  change (composeValueMap A B C E (𝟙 (BimoduleCategory.of A B C P))
      (rightBimoduleUnitIso A C E Q).hom b e).f n
      ((associatorValueIso A B C E E P Q (Bimodule.diagonal A E) b e).hom.f n
        (associatorLeftElement A B C E E P Q (Bimodule.diagonal A E) b c e' e t q v hi hn)) = _
  rw [associatorValueIso_hom_element A B C E E P Q (Bimodule.diagonal A E)
    b c e' e t q v hi (show k + r = k + r from rfl) hn]
  change (composeValueMap A B C E (𝟙 (BimoduleCategory.of A B C P))
      (rightBimoduleUnitIso A C E Q).hom b e).f n
      (BalancedTensor.element A C _ _ c
        (BalancedTensor.element A E (representable A e) (Q.leftAt c) e' t q rfl) v (by omega)) =
    (BalancedTensor.yonedaEvaluation A E e ((compose A B C E P Q).leftAt b)).f n
      (BalancedTensor.element A E (representable A e) ((compose A B C E P Q).leftAt b) e' t
        (BalancedTensor.element A C (Q.rightAt e') (P.leftAt b) c q v hi) hn)
  erw [composeValueMap_element A B C E (𝟙 (BimoduleCategory.of A B C P))
    (rightBimoduleUnitIso A C E Q).hom b c e
    (BalancedTensor.element A E (representable A e) (Q.leftAt c) e' t q rfl) v (by omega),
    rightBimoduleUnitIso_hom_value]
  simp only [CategoryTheory.Functor.map_id]
  rw [BalancedTensor.yonedaEvaluation_element]
  change BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) c (n := n)
    ((BalancedTensor.yonedaEvaluation A E e (Q.leftAt c)).f (k + r)
      (BalancedTensor.element A E (representable A e) (Q.leftAt c) e' t q rfl)) v (by omega) =
    leftAction A ((compose A B C E P Q).leftAt b) (n := n) t
      (BalancedTensor.element A C (Q.rightAt e') (P.leftAt b) c q v hi) (by omega)
  rw [BalancedTensor.yonedaEvaluation_element]
  exact (compose_leftAction_element A B C E P Q b c e' e
    (p := k) (k := r) (r := s) (i := i) (j := k + r) (n := n)
    hi (by omega) (by omega) t q v).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end RightUnitAssociativity

/-! ## RightUnitAssociativityBimodule（旧 SerrePositivity/DifferentialGraded/Tensor/RightUnitAssociativityBimodule.lean） -/

/-!
概要：右 Yoneda 単位と結合の値ごとの整合性を実双加群射の整合性へ束ねる。
方針：全値への評価の忠実性と既存の tensor 双関手を使う。
規約：元の実結合同型と単位同型を保持する。
使われ方：D-19 の graph 作用の代表上の合成比較。
-/

@[expose] public section RightUnitAssociativityBimodule
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [Small.{u} B] [DGCategory A C] [Small.{u} C]
  [DGCategory A E] [Small.{u} E] (P : Bimodule A B C) (Q : Bimodule A C E)

lemma rightUnit_associator :
    (associatorIso A B C E E P Q (Bimodule.diagonal A E)).hom ≫
      composeMap A B C E (𝟙 (BimoduleCategory.of A B C P))
        (rightBimoduleUnitIso A C E Q).hom =
    (rightBimoduleUnitIso A B E (compose A B C E P Q)).hom := by
  apply BimoduleCategory.value_hom_ext A B E
  intro b e
  simp only [CategoryTheory.Functor.map_comp, associatorIso_hom_value_eval,
    composeMap_value_eval, rightBimoduleUnitIso_hom_value]
  exact rightUnit_associator_value A B C E P Q b e

lemma rightUnit_associator_inv :
    (associatorIso A B C E E P Q (Bimodule.diagonal A E)).inv ≫
      (rightBimoduleUnitIso A B E (compose A B C E P Q)).hom =
    composeMap A B C E (𝟙 (BimoduleCategory.of A B C P))
      (rightBimoduleUnitIso A C E Q).hom := by
  rw [← rightUnit_associator A B C E P Q, Iso.inv_hom_id_assoc]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end RightUnitAssociativityBimodule

/-! ## ComposeLeftRestriction（旧 SerrePositivity/DifferentialGraded/Tensor/ComposeLeftRestriction.lean） -/

/-! # 合成の外側の左dg作用の制限と相対tensor合成の可換性

## 概要
合成の外側の左dg作用の制限と相対tensor合成の可換性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section ComposeLeftRestriction
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E]
  (D : Type t) [DGCategory A D] (F : DGFunctor A D E)

/-- 外側の左作用の制限は相対tensor合成の全Hom作用と可換。 -/
lemma compose_leftRestriction (P : Bimodule A B C) (Q : Bimodule A C E) :
    compose A B C D P (Bimodule.leftRestriction A C E D F Q) =
      Bimodule.leftRestriction A B E D F (compose A B C E P Q) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := compose A B C D P (Bimodule.leftRestriction A C E D F Q))
    (G := Bimodule.leftRestriction A B E D F (compose A B C E P Q)) (fun _ => rfl)
  intro d d'
  simp only [eqToHom_refl, Category.comp_id]
  apply moduleHom_ext
  intro b
  refine (compose_leftMap_π A B C D P (Bimodule.leftRestriction A C E D F Q) d d' b).trans ?_
  change ((F.map d d' ≫ Q.map (F.obj d) (F.obj d')) ≫
      BalancedTensor.rightHomMap A C (Q.rightAt (F.obj d)) (Q.rightAt (F.obj d'))
        (P.leftAt b)) =
    (F.map d d' ≫ (compose A B C E P Q).map (F.obj d) (F.obj d')) ≫
      moduleHomπ A B _ _ b
  rw [Category.assoc]
  exact congrArg (fun k => F.map d d' ≫ k)
    (compose_leftMap_π A B C E P Q (F.obj d) (F.obj d') b).symm

/-- 合成の外側の左作用の制限を交換する、既存bimodule対象間の同型。 -/
def composeLeftRestrictionIso (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) :
    BimoduleCategory.of A B D
        (compose A B C D (BimoduleCategory.underlying A B C P)
          (Bimodule.leftRestriction A C E D F (BimoduleCategory.underlying A C E Q))) ≅
      (BimoduleCategory.middleLeftRestrictionFunctor A B E D F).obj
        (BimoduleCategory.of A B E (compose A B C E
          (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q))) :=
  eqToIso (compose_leftRestriction A B C E D F _ _)

@[simp]
lemma composeLeftRestrictionIso_hom_value
    (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (b : B) (d : D) :
    (BimoduleCategory.valueEvaluation A B D b d).map
        (composeLeftRestrictionIso A B C E D F P Q).hom = 𝟙 _ := by
  simp only [composeLeftRestrictionIso, eqToIso.hom, eqToHom_map]
  rfl

/-- 外側の制限の比較は、両因子の任意の全Hom自然な閉零射に自然。 -/
lemma composeLeftRestrictionIso_naturality
    {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    composeMap A B C D f ((BimoduleCategory.middleLeftRestrictionFunctor A C E D F).map g) ≫
        (composeLeftRestrictionIso A B C E D F P' Q').hom =
      (composeLeftRestrictionIso A B C E D F P Q).hom ≫
        (BimoduleCategory.middleLeftRestrictionFunctor A B E D F).map
          (composeMap A B C E f g) := by
  apply BimoduleCategory.value_hom_ext A B D
  intro b d
  simp only [CategoryTheory.Functor.map_comp, composeLeftRestrictionIso_hom_value,
    composeMap_value_eval]
  erw [Category.comp_id, Category.id_comp]
  change composeValueMap A B C D f
      ((BimoduleCategory.middleLeftRestrictionFunctor A C E D F).map g) b d =
    (BimoduleCategory.valueEvaluation A B E b (F.obj d)).map (composeMap A B C E f g)
  rw [composeMap_value_eval]
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end ComposeLeftRestriction

/-! ## ComposeRightRestrictionValue（旧 SerrePositivity/DifferentialGraded/Tensor/ComposeRightRestrictionValue.lean） -/

/-! # 外側右作用制限と相対tensor合成の値の比較

## 概要
外側右作用制限と相対tensor合成の値の比較。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section ComposeRightRestrictionValue
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D B)

/-- 外側の右作用を制限してから合成した値を、合成後に制限した値へ送る同型。 -/
def composeRightRestrictionValueIso (P : Bimodule A B C) (Q : Bimodule A C E) (d : D) (e : E) :
    (compose A D C E (Bimodule.rightRestriction A B D C F P) Q).value d e ≅
      (compose A B C E P Q).value (F.obj d) e :=
  (BalancedTensor.leftTensorFunctor A C (Q.rightAt e)).mapIso
    (Bimodule.rightRestrictionLeftEvaluationIso A B D C F (BimoduleCategory.of A B C P) d)

@[reassoc]
lemma ι_composeRightRestrictionValueIso_hom (P : Bimodule A B C) (Q : Bimodule A C E)
    (d : D) (e : E) (c : C) :
    BalancedTensor.ι A C (Q.rightAt e) ((Bimodule.rightRestriction A B D C F P).leftAt d) c ≫
        (composeRightRestrictionValueIso A B D C E F P Q d e).hom =
      BalancedTensor.ι A C (Q.rightAt e) (P.leftAt (F.obj d)) c := by
  change BalancedTensor.ι A C (Q.rightAt e)
      ((Bimodule.rightRestriction A B D C F P).leftAt d) c ≫
      BalancedTensor.map A C (𝟙 (ForgetEnrichment.of (Complex A) (Q.rightAt e)))
        (Bimodule.rightRestrictionLeftEvaluationIso A B D C F
          (BimoduleCategory.of A B C P) d).hom = _
  have h := BalancedTensor.ι_map A C
    (M := ForgetEnrichment.of (Complex A) (Q.rightAt e))
    (M' := ForgetEnrichment.of (Complex A) (Q.rightAt e))
    (N := (BimoduleCategory.leftEvaluation A D C d).obj
      ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).obj
        (BimoduleCategory.of A B C P)))
    (N' := (BimoduleCategory.leftEvaluation A B C (F.obj d)).obj
      (BimoduleCategory.of A B C P))
    (𝟙 (ForgetEnrichment.of (Complex A) (Q.rightAt e)))
    (Bimodule.rightRestrictionLeftEvaluationIso A B D C F
      (BimoduleCategory.of A B C P) d).hom c
  simp only [CategoryTheory.Functor.map_id,
    Bimodule.rightRestrictionLeftEvaluationIso_hom_eval, tensorHom_id, id_whiskerRight] at h
  exact h.trans (Category.id_comp (BalancedTensor.ι A C (Q.rightAt e) (P.leftAt (F.obj d)) c))

lemma composeRightRestrictionValueIso_element (P : Bimodule A B C) (Q : Bimodule A C E)
    (d : D) (c : C) (e : E) {r s n : ℤ} (hn : r + s = n)
    (q : (Q.value c e).X r) (p : (P.value (F.obj d) c).X s) :
    (composeRightRestrictionValueIso A B D C E F P Q d e).hom.f n
        (BalancedTensor.element A C (Q.rightAt e)
          ((Bimodule.rightRestriction A B D C F P).leftAt d) c q p hn) =
      BalancedTensor.element A C (Q.rightAt e) (P.leftAt (F.obj d)) c q p hn :=
  BalancedTensor.element_postcompose A C (Q.rightAt e)
    ((Bimodule.rightRestriction A B D C F P).leftAt d) c _ _
    (ι_composeRightRestrictionValueIso_hom A B D C E F P Q d e c) q p hn

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end ComposeRightRestrictionValue

/-! ## ComposeRightRestrictionActions（旧 SerrePositivity/DifferentialGraded/Tensor/ComposeRightRestrictionActions.lean） -/

/-! # 外側右制限のtensor比較と残る全次数作用の可換性

## 概要
外側右制限のtensor比較と残る全次数作用の可換性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section ComposeRightRestrictionActions
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D B)
  (P : Bimodule A B C) (Q : Bimodule A C E)

/-- 右作用のKoszul符号は、制限前後で同じ次数積を持つ。 -/
lemma composeRightRestrictionValueIso_rightAction
    (d d' : Dᵒᵖ) (c : C) (e : E) {p k r i j n : ℤ}
    (ha : k + r = i) (hj : r + p = j) (hn : i + p = n)
    (g : GradedHom A d d' p) (q : (Q.value c e).X k)
    (v : (P.value (F.obj d.unop) c).X r) :
    (composeRightRestrictionValueIso A B D C E F P Q d'.unop e).hom.f n
        (moduleAction A ((compose A D C E (Bimodule.rightRestriction A B D C F P) Q).rightAt e)
          g (BalancedTensor.element A C (Q.rightAt e)
            ((Bimodule.rightRestriction A B D C F P).leftAt d.unop) c q v ha) hn) =
      moduleAction A ((Bimodule.rightRestriction A B D E F (compose A B C E P Q)).rightAt e)
        g ((composeRightRestrictionValueIso A B D C E F P Q d.unop e).hom.f i
          (BalancedTensor.element A C (Q.rightAt e)
            ((Bimodule.rightRestriction A B D C F P).leftAt d.unop) c q v ha)) hn := by
  rw [compose_rightAction_element A D C E (Bimodule.rightRestriction A B D C F P) Q
    d d' c e ha hj hn]
  simp only [Units.smul_def, map_zsmul]
  rw [composeRightRestrictionValueIso_element, composeRightRestrictionValueIso_element]
  exact (compose_rightAction_element A B C E P Q (F.op.obj d) (F.op.obj d') c e ha hj hn
    ((F.op.map d d').f p g) q v).symm

lemma composeRightRestrictionValueIso_leftAction
    (d : D) (c : C) (e e' : E) {p k r i j n : ℤ}
    (ha : k + r = i) (hj : k + p = j) (hn : i + p = n)
    (g : GradedHom A e e' p) (q : (Q.value c e).X k)
    (v : (P.value (F.obj d) c).X r) :
    (composeRightRestrictionValueIso A B D C E F P Q d e').hom.f n
        (SerrePositivity.DifferentialGraded.leftAction A
          ((compose A D C E (Bimodule.rightRestriction A B D C F P) Q).leftAt d) g
          (BalancedTensor.element A C (Q.rightAt e)
            ((Bimodule.rightRestriction A B D C F P).leftAt d) c q v ha) hn) =
      SerrePositivity.DifferentialGraded.leftAction A
        ((Bimodule.rightRestriction A B D E F (compose A B C E P Q)).leftAt d) g
        ((composeRightRestrictionValueIso A B D C E F P Q d e).hom.f i
          (BalancedTensor.element A C (Q.rightAt e)
            ((Bimodule.rightRestriction A B D C F P).leftAt d) c q v ha)) hn := by
  rw [compose_leftAction_element A D C E (Bimodule.rightRestriction A B D C F P) Q
    d c e e' ha hj hn, composeRightRestrictionValueIso_element,
    composeRightRestrictionValueIso_element, Bimodule.rightRestriction_leftAction,
    compose_leftAction_element A B C E P Q (F.obj d) c e e' ha hj hn]

lemma composeRightRestrictionValueIso_right_naturality (d d' : Dᵒᵖ) (e : E) :
    ((compose A D C E (Bimodule.rightRestriction A B D C F P) Q).rightAt e).map d d' ≫
        homPostcompose _ (composeRightRestrictionValueIso A B D C E F P Q d'.unop e).hom =
      ((Bimodule.rightRestriction A B D E F (compose A B C E P Q)).rightAt e).map d d' ≫
        homPrecompose (composeRightRestrictionValueIso A B D C E F P Q d.unop e).hom _ := by
  apply BalancedTensor.homMap_post_pre_eq A C (Q.rightAt e)
    ((Bimodule.rightRestriction A B D C F P).leftAt d.unop)
  intro p g c k r i n ha hn q v
  exact composeRightRestrictionValueIso_rightAction A B D C E F P Q d d' c e
    (j := r + p) ha rfl hn g q v

lemma composeRightRestrictionValueIso_left_naturality (d : D) (e e' : E) :
    ((compose A D C E (Bimodule.rightRestriction A B D C F P) Q).leftAt d).map e e' ≫
        homPostcompose _ (composeRightRestrictionValueIso A B D C E F P Q d e').hom =
      ((Bimodule.rightRestriction A B D E F (compose A B C E P Q)).leftAt d).map e e' ≫
        homPrecompose (composeRightRestrictionValueIso A B D C E F P Q d e).hom _ := by
  apply BalancedTensor.homMap_post_pre_eq A C (Q.rightAt e)
    ((Bimodule.rightRestriction A B D C F P).leftAt d)
  intro p g c k r i n ha hn q v
  exact composeRightRestrictionValueIso_leftAction A B D C E F P Q d c e e'
    (j := k + p) ha rfl hn g q v

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end ComposeRightRestrictionActions

/-! ## ComposeRightRestriction（旧 SerrePositivity/DifferentialGraded/Tensor/ComposeRightRestriction.lean） -/

/-! # 外側右作用制限と相対tensor合成の全Hom自然な比較同型

## 概要
外側右作用制限と相対tensor合成の全Hom自然な比較同型。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section ComposeRightRestriction
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D B)

/-- 値の比較を、外側右作用の全Homと可換な右加群同型へ束ねる。 -/
def composeRightRestrictionRightIso (P : Bimodule A B C) (Q : Bimodule A C E) (e : E) :
    ForgetEnrichment.of (Complex A)
        ((compose A D C E (Bimodule.rightRestriction A B D C F P) Q).rightAt e) ≅
      ForgetEnrichment.of (Complex A)
        ((Bimodule.rightRestriction A B D E F (compose A B C E P Q)).rightAt e) :=
  moduleIsoMk A D (fun d => composeRightRestrictionValueIso A B D C E F P Q d.unop e)
    (fun d d' => composeRightRestrictionValueIso_right_naturality A B D C E F P Q d d' e)

/-- 右作用制限と合成の比較は、残る左作用も全Homで保つ実際のbimodule同型。 -/
def composeRightRestrictionIso (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) :
    BimoduleCategory.of A D E
        (compose A D C E
          (Bimodule.rightRestriction A B D C F (BimoduleCategory.underlying A B C P))
          (BimoduleCategory.underlying A C E Q)) ≅
      (BimoduleCategory.middleRightRestrictionFunctor A B D E F).obj
        (BimoduleCategory.of A B E (compose A B C E
          (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q))) :=
  BimoduleCategory.isoOfValueFamily A D E
    (fun e => composeRightRestrictionRightIso A B D C E F
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) e) (by
    intro d e e'
    simp only [composeRightRestrictionRightIso, moduleIsoMk_hom_eval]
    exact composeRightRestrictionValueIso_left_naturality A B D C E F
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) d e e')

@[simp]
lemma composeRightRestrictionIso_hom_value (P : BimoduleCategory A B C)
    (Q : BimoduleCategory A C E) (d : D) (e : E) :
    (BimoduleCategory.valueEvaluation A D E d e).map
        (composeRightRestrictionIso A B D C E F P Q).hom =
      (composeRightRestrictionValueIso A B D C E F
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) d e).hom := by
  change (moduleEvaluation A D d).map
    (composeRightRestrictionRightIso A B D C E F
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) e).hom = _
  simp only [composeRightRestrictionRightIso, moduleIsoMk_hom_eval]

@[simp]
lemma composeRightRestrictionIso_inv_value (P : BimoduleCategory A B C)
    (Q : BimoduleCategory A C E) (d : D) (e : E) :
    (BimoduleCategory.valueEvaluation A D E d e).map
        (composeRightRestrictionIso A B D C E F P Q).inv =
      (composeRightRestrictionValueIso A B D C E F
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) d e).inv := by
  change (moduleEvaluation A D d).map
    (composeRightRestrictionRightIso A B D C E F
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) e).inv = _
  simp only [composeRightRestrictionRightIso, moduleIsoMk_inv_eval]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end ComposeRightRestriction

/-! ## ComposeRightRestrictionNaturality（旧 SerrePositivity/DifferentialGraded/Tensor/ComposeRightRestrictionNaturality.lean） -/

/-! # 外側右制限の合成比較と両因子の閉零射の自然性

## 概要
外側右制限の合成比較と両因子の閉零射の自然性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section ComposeRightRestrictionNaturality
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D B)

/-- 外側右制限と合成の比較は、両因子の任意の全Hom自然な閉零射に自然。 -/
lemma composeRightRestrictionIso_naturality
    {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    composeMap A D C E ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).map f) g ≫
        (composeRightRestrictionIso A B D C E F P' Q').hom =
      (composeRightRestrictionIso A B D C E F P Q).hom ≫
        (BimoduleCategory.middleRightRestrictionFunctor A B D E F).map
          (composeMap A B C E f g) := by
  apply BimoduleCategory.value_hom_ext A D E
  intro d e
  simp only [CategoryTheory.Functor.map_comp, composeMap_value_eval,
    composeRightRestrictionIso_hom_value]
  refine Eq.trans ?_ (congrArg (fun k =>
    (composeRightRestrictionValueIso A B D C E F
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) d e).hom ≫ k)
    (BimoduleCategory.middleRightRestrictionMap_value_eval A B D E F
      (composeMap A B C E f g) d e)).symm
  rw [composeMap_value_eval]
  apply BalancedTensor.hom_ext A C ((BimoduleCategory.underlying A C E Q).rightAt e)
    ((Bimodule.rightRestriction A B D C F (BimoduleCategory.underlying A B C P)).leftAt d)
  intro c
  have h₁ := ι_composeValueMap A D C E
    ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).map f) g d c e
  have h₂ := ι_composeRightRestrictionValueIso_hom A B D C E F
    (BimoduleCategory.underlying A B C P') (BimoduleCategory.underlying A C E Q') d e c
  have h₃ := ι_composeRightRestrictionValueIso_hom A B D C E F
    (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) d e c
  have h₄ := ι_composeValueMap A B C E f g (F.obj d) c e
  have hl := (congrArg (fun k => k ≫
      (composeRightRestrictionValueIso A B D C E F
        (BimoduleCategory.underlying A B C P')
        (BimoduleCategory.underlying A C E Q') d e).hom) h₁).trans (by
    simpa only [Category.assoc, BimoduleCategory.middleRightRestrictionFunctor,
      BimoduleCategory.underlying, BimoduleCategory.of] using congrArg (fun k =>
      ((BimoduleCategory.valueEvaluation A C E c e).map g ⊗ₘ
        (BimoduleCategory.valueEvaluation A D C d c).map
          ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).map f)) ≫ k) h₂)
  have hr := (congrArg (fun k => k ≫ composeValueMap A B C E f g (F.obj d) e) h₃).trans h₄
  have hm := congrArg (fun k => ((BimoduleCategory.valueEvaluation A C E c e).map g ⊗ₘ k) ≫
    BalancedTensor.ι A C ((BimoduleCategory.underlying A C E Q').rightAt e)
      ((BimoduleCategory.underlying A B C P').leftAt (F.obj d)) c)
    (BimoduleCategory.middleRightRestrictionMap_value_eval A B D C F f d c)
  simpa only [Category.assoc, BimoduleCategory.middleRightRestrictionFunctor,
      BimoduleCategory.underlying, BimoduleCategory.of] using hl.trans (hm.trans hr.symm)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end ComposeRightRestrictionNaturality
