module

public import SerrePositivity.DifferentialGraded.Derived.KFlat
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtension
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Functor.Closed
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensor

/-!
# Derived.BimoduleComposition.Resolution

## 概要
導来合成の解像度計算、両単位と結合比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## BimoduleRestriction（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleRestriction.lean） -/

/-! # 両dg圏の関手に沿う導来bimodule制限

## 概要
既存の積dg圏との同値を用い、全Hom自然な主bimodule圏へ制限を戻す。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleRestriction
universe u v w z t

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A B D) (G : DGFunctor A C E)

/-- Bᵒᵖ⊗Cのopposite上の右加群を制限するための二重opposite関手。 -/
def bimoduleRestrictionIndex :
    DGFunctor A (DGTensorCategory A Bᵒᵖ C)ᵒᵖᵒᵖ (DGTensorCategory A Dᵒᵖ E)ᵒᵖᵒᵖ :=
  (F.op.tensor G).op.op

/-- 全次数の二作用を保持する制限関手。 -/
def bimoduleRestriction : BimoduleCategory A D E ⥤ BimoduleCategory A B C :=
  (rightModuleBimoduleEquivalence A D E).inverse ⋙
    moduleRestriction A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (DGTensorCategory A Dᵒᵖ E)ᵒᵖ
      (bimoduleRestrictionIndex A B C D E F G) ⋙
    (rightModuleBimoduleEquivalence A B C).functor

lemma bimoduleRestriction_quasiIso {M N : BimoduleCategory A D E} (f : M ⟶ N)
    (hf : BimoduleCategory.quasiIso A D E f) :
    BimoduleCategory.quasiIso A B C ((bimoduleRestriction A B C D E F G).map f) :=
  (rightModuleBimoduleEquivalence_quasiIso_iff A B C _).2
    (moduleRestriction_quasiIso A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
      (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (bimoduleRestrictionIndex A B C D E F G) _
      ((rightModuleBimodule_inverse_quasiIso_iff A D E f).2 hf))

/-- 対象ごとの準同型保存から得る、置換不要の導来制限。 -/
def derivedBimoduleRestriction :
    DerivedBimoduleCategory A D E ⥤ DerivedBimoduleCategory A B C :=
  bimoduleDerivedLift A D E
    (bimoduleRestriction A B C D E F G ⋙ bimoduleToDerived A B C) (by
      intro M N f hf
      exact bimoduleToDerived_inverts A B C _ (bimoduleRestriction_quasiIso A B C D E F G f hf))

lemma derivedBimoduleRestriction_fac :
    bimoduleToDerived A D E ⋙ derivedBimoduleRestriction A B C D E F G =
      bimoduleRestriction A B C D E F G ⋙ bimoduleToDerived A B C :=
  bimoduleDerivedLift_fac _ _ _ _ _

end SerrePositivity.DifferentialGraded
end

end BimoduleRestriction

/-! ## BimoduleRestrictionEvaluation（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleRestrictionEvaluation.lean） -/

/-! # 両側制限とbimodule値評価の自然比較

## 概要
両側制限とbimodule値評価の自然比較。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleRestrictionEvaluation
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]

/-- 積dg圏表示へ移ってからの評価は元のbimodule値と自然同型。 -/
def bimoduleRightModuleEvaluationIso (b : B) (c : C) :
    (rightModuleBimoduleEquivalence A B C).inverse ⋙
        moduleEvaluation A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (op (op b, c)) ≅
      BimoduleCategory.valueEvaluation A B C b c :=
  Functor.isoWhiskerLeft (rightModuleBimoduleEquivalence A B C).inverse
      (rightModuleBimoduleEvaluationIso A B C b c).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rightModuleBimoduleEquivalence A B C).counitIso
      (BimoduleCategory.valueEvaluation A B C b c) ≪≫
    Functor.leftUnitor _

variable (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A B D) (G : DGFunctor A C E)

def bimoduleRestrictionEvaluationIso (b : B) (c : C) :
    bimoduleRestriction A B C D E F G ⋙ BimoduleCategory.valueEvaluation A B C b c ≅
      BimoduleCategory.valueEvaluation A D E (F.obj b) (G.obj c) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (rightModuleBimoduleEquivalence A D E).inverse
      (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft (rightModuleBimoduleEquivalence A D E).inverse
      (Functor.isoWhiskerLeft
        (moduleRestriction A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
          (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (bimoduleRestrictionIndex A B C D E F G))
        (rightModuleBimoduleEvaluationIso A B C b c)) ≪≫
    Functor.isoWhiskerLeft (rightModuleBimoduleEquivalence A D E).inverse
      (moduleRestrictionEvaluationIso A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
        (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (bimoduleRestrictionIndex A B C D E F G)
        (op (op b, c))) ≪≫
    bimoduleRightModuleEvaluationIso A D E (F.obj b) (G.obj c)

end SerrePositivity.DifferentialGraded
end

end BimoduleRestrictionEvaluation

/-! ## BimoduleComposition（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleComposition.lean） -/

/-! # 両変数の全導来bimodule圏上の合成とK-flat因子での計算

## 概要
両変数の全導来bimodule圏上の合成とK-flat因子での計算。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionResolution.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleComposition
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

/-- 後因子Qを外変数とする導来合成。両変数とも指定準同型の全局所化上にある。 -/
def derivedBimoduleComposeFunctor (hE : localHomKFlat A E) :
    DerivedBimoduleCategory A C E ⥤
      (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) :=
  derivedRightKFlatReplacement A C E hE ⋙ rightFactorLocalizedComposeFunctor A B C E

/-- K-flat部分圏の局所化へ制限すると既存の固定因子関手族と自然同型になる。 -/
def derivedBimoduleComposeKFlatFamilyIso (hE : localHomKFlat A E) :
    rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE ≅
      rightFactorLocalizedComposeFunctor A B C E :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rightKFlatReplacementUnitIso A C E hE)
      (rightFactorLocalizedComposeFunctor A B C E) ≪≫
    Functor.leftUnitor (rightFactorLocalizedComposeFunctor A B C E)

def derivedBimoduleComposeKFlatIso (hE : localHomKFlat A E)
    (Q : RightKFlatBimoduleCategory A C E) :
    (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj) ≅
      derivedComposeWith A B C E Q.obj Q.property :=
  (derivedBimoduleComposeKFlatFamilyIso A B C E hE).app ((rightKFlatToDerived A C E).obj Q)

def derivedBimoduleComposeKFlatValueIso (hE : localHomKFlat A E)
    (Q : RightKFlatBimoduleCategory A C E) (P : BimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj)).obj
        ((bimoduleToDerived A B C).obj P) ≅
      (bimoduleToDerived A B E).obj (BimoduleCategory.of A B E
        (compose A B C E (BimoduleCategory.underlying A B C P)
          (BimoduleCategory.underlying A C E Q.obj))) :=
  (derivedBimoduleComposeKFlatIso A B C E hE Q).app ((bimoduleToDerived A B C).obj P)

/-- 任意の指定された右K-flat解像度で、同じ導来合成関手を計算できる。 -/
def derivedBimoduleComposeResolutionComputation (hE : localHomKFlat A E)
    (Q : BimoduleCategory A C E) (R : RightKFlatBimoduleCategory A C E)
    (q : R.obj ⟶ Q) (hq : BimoduleCategory.quasiIso A C E q) :
    (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q) ≅
      derivedComposeWith A B C E R.obj R.property :=
  (derivedBimoduleComposeFunctor A B C E hE).mapIso (bimoduleDerivedIso A C E q hq).symm ≪≫
    derivedBimoduleComposeKFlatIso A B C E hE R

lemma derivedBimoduleComposeKFlatIso_naturality (hE : localHomKFlat A E)
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    (derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map g.hom) ≫
        (derivedBimoduleComposeKFlatIso A B C E hE Q').hom =
      (derivedBimoduleComposeKFlatIso A B C E hE Q).hom ≫
        derivedComposeWithMap A B C E Q.property Q'.property g.hom := by
  have h := (derivedBimoduleComposeKFlatFamilyIso A B C E hE).hom.naturality
    ((rightKFlatToDerived A C E).map g)
  change (derivedBimoduleComposeFunctor A B C E hE).map
      ((rightKFlatDerivedInclusion A C E).map ((rightKFlatToDerived A C E).map g)) ≫ _ =
    _ ≫ (rightFactorLocalizedComposeFunctor A B C E).map ((rightKFlatToDerived A C E).map g) at h
  rw [rightKFlatDerivedInclusion_map_base, rightFactorLocalizedComposeFunctor_map_base] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleComposition

/-! ## BimoduleCompositionResolution（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionResolution.lean） -/

/-! # 全導来合成の解像度計算同型と増大射・比較squareの整合性

## 概要
全導来合成の解像度計算同型と増大射・比較squareの整合性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionPairResolution.lean、
Derived/BimoduleCompositionResolutionValues.lean、Derived/BimoduleCompositionRightUnit.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionResolution
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

lemma derivedBimoduleComposeResolutionComputation_fac (hE : localHomKFlat A E)
    (Q : BimoduleCategory A C E) (R : RightKFlatBimoduleCategory A C E)
    (q : R.obj ⟶ Q) (hq : BimoduleCategory.quasiIso A C E q) :
    (derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map q) ≫
        (derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq).hom =
      (derivedBimoduleComposeKFlatIso A B C E hE R).hom := by
  change (derivedBimoduleComposeFunctor A B C E hE).map
      (bimoduleDerivedIso A C E q hq).hom ≫
    ((derivedBimoduleComposeFunctor A B C E hE).map
      (bimoduleDerivedIso A C E q hq).inv ≫ _) = _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

lemma derivedBimoduleComposeResolutionComputation_self (hE : localHomKFlat A E)
    (R : RightKFlatBimoduleCategory A C E) :
    derivedBimoduleComposeResolutionComputation A B C E hE R.obj R (𝟙 R.obj)
        ((BimoduleCategory.quasiIso A C E).id_mem R.obj) =
      derivedBimoduleComposeKFlatIso A B C E hE R := by
  apply Iso.ext
  have h := derivedBimoduleComposeResolutionComputation_fac A B C E hE R.obj R (𝟙 R.obj)
    ((BimoduleCategory.quasiIso A C E).id_mem R.obj)
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using h

/-- 増大squareは導来圏で可換ならよく、閉零圏での厳密な可換性を要求しない。 -/
lemma derivedBimoduleComposeResolutionComputation_naturality (hE : localHomKFlat A E)
    {Q Q' : BimoduleCategory A C E} (R S : RightKFlatBimoduleCategory A C E)
    (q : R.obj ⟶ Q) (r : S.obj ⟶ Q')
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A C E r)
    (f : Q ⟶ Q') (g : R ⟶ S)
    (h : (bimoduleToDerived A C E).map q ≫ (bimoduleToDerived A C E).map f =
      (bimoduleToDerived A C E).map g.hom ≫ (bimoduleToDerived A C E).map r) :
    (derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map f) ≫
        (derivedBimoduleComposeResolutionComputation A B C E hE Q' S r hr).hom =
      (derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq).hom ≫
        derivedComposeWithMap A B C E R.property S.property g.hom := by
  apply (Iso.cancel_iso_hom_left
    ((derivedBimoduleComposeFunctor A B C E hE).mapIso (bimoduleDerivedIso A C E q hq)) _ _).1
  change (derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map q) ≫
      ((derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map f) ≫
        (derivedBimoduleComposeResolutionComputation A B C E hE Q' S r hr).hom) =
    (derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map q) ≫
      ((derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq).hom ≫
        derivedComposeWithMap A B C E R.property S.property g.hom)
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, h,
    CategoryTheory.Functor.map_comp, Category.assoc,
    derivedBimoduleComposeResolutionComputation_fac]
  rw [← Category.assoc, derivedBimoduleComposeResolutionComputation_fac]
  exact derivedBimoduleComposeKFlatIso_naturality A B C E hE g

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionResolution

/-! ## BimoduleCompositionResolutionValues（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionResolutionValues.lean） -/

/-! # 指定解像度による導来合成の値の計算と増大squareの整合性

## 概要
指定解像度による導来合成の値の計算と増大squareの整合性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionValueNaturality.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionResolutionValues
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]

omit [Small.{u} E] in
lemma derivedComposeWithMap_computation {R S : RightKFlatBimoduleCategory A C E}
    (r : R ⟶ S) (P : BimoduleCategory A B C) :
    (derivedComposeWithMap A B C E R.property S.property r.hom).app
        ((bimoduleToDerived A B C).obj P) ≫
      (derivedComposeWithComputation A B C E S.obj S.property P).hom =
    (derivedComposeWithComputation A B C E R.obj R.property P).hom ≫
      (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) r.hom) := by
  rw [derivedComposeWithMap_app]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 全導来合成の指定解像度による値での計算同型。 -/
def derivedBimoduleComposeResolutionValueIso (hE : localHomKFlat A E)
    (Q : BimoduleCategory A C E) (R : RightKFlatBimoduleCategory A C E)
    (q : R.obj ⟶ Q) (hq : BimoduleCategory.quasiIso A C E q) (P : BimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q)).obj
        ((bimoduleToDerived A B C).obj P) ≅
      (bimoduleToDerived A B E).obj ((composeWith A B C E R.obj).obj P) :=
  (derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq).app
    ((bimoduleToDerived A B C).obj P) ≪≫
      derivedComposeWithComputation A B C E R.obj R.property P

/-- 増大squareの導来可換性から、値の計算同型の変換則を得る。 -/
lemma derivedBimoduleComposeResolutionValueIso_change (hE : localHomKFlat A E)
    (Q : BimoduleCategory A C E) (R S : RightKFlatBimoduleCategory A C E)
    (q : R.obj ⟶ Q) (s : S.obj ⟶ Q)
    (hq : BimoduleCategory.quasiIso A C E q) (hs : BimoduleCategory.quasiIso A C E s)
    (r : R ⟶ S)
    (h : (bimoduleToDerived A C E).map q =
      (bimoduleToDerived A C E).map r.hom ≫ (bimoduleToDerived A C E).map s)
    (P : BimoduleCategory A B C) :
    (derivedBimoduleComposeResolutionValueIso A B C E hE Q S s hs P).hom =
      (derivedBimoduleComposeResolutionValueIso A B C E hE Q R q hq P).hom ≫
        (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) r.hom) := by
  have hn := derivedBimoduleComposeResolutionComputation_naturality A B C E hE
    R S q s hq hs (𝟙 Q) r (by
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact h)
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hn
  have hv := NatTrans.congr_app hn ((bimoduleToDerived A B C).obj P)
  change (derivedBimoduleComposeResolutionComputation A B C E hE Q S s hs).hom.app
      ((bimoduleToDerived A B C).obj P) =
    (derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq).hom.app
      ((bimoduleToDerived A B C).obj P) ≫
        (derivedComposeWithMap A B C E R.property S.property r.hom).app
          ((bimoduleToDerived A B C).obj P) at hv
  dsimp only [derivedBimoduleComposeResolutionValueIso, Iso.trans_hom]
  simp only [Iso.app_hom]
  rw [hv, Category.assoc, derivedComposeWithMap_computation, ← Category.assoc]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionResolutionValues

/-! ## BimoduleCompositionRightUnit（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionRightUnit.lean） -/

/-! # 全後因子上の導来bimodule合成の右単位自然同型

## 概要
全後因子上の導来bimodule合成の右単位自然同型。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionLeftUnit.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionRightUnit
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

omit [DGCategory A B] [Small.{u} B] in
def rightKFlatDiagonal : RightKFlatBimoduleCategory A C C :=
  ⟨BimoduleCategory.of A C C (Bimodule.diagonal A C), Bimodule.diagonal_rightRelativeKFlat A C⟩

def derivedBimoduleRightUnitIso (hC : localHomKFlat A C) :
    (derivedBimoduleComposeFunctor A B C C hC).obj
        ((bimoduleToDerived A C C).obj (rightKFlatDiagonal A C).obj) ≅
      𝟭 (DerivedBimoduleCategory A B C) :=
  derivedBimoduleComposeKFlatIso A B C C hC (rightKFlatDiagonal A C) ≪≫ derivedRightUnitIso A B C

lemma derivedBimoduleRightUnitIso_base_app (hC : localHomKFlat A C) (P : BimoduleCategory A B C) :
    (derivedBimoduleRightUnitIso A B C hC).hom.app ((bimoduleToDerived A B C).obj P) =
      (derivedBimoduleComposeKFlatValueIso A B C C hC (rightKFlatDiagonal A C) P).hom ≫
        (bimoduleToDerived A B C).map
          (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom := by
  change (derivedBimoduleComposeKFlatValueIso A B C C hC (rightKFlatDiagonal A C) P).hom ≫
    (derivedRightUnitIso A B C).hom.app ((bimoduleToDerived A B C).obj P) = _
  rw [derivedRightUnitIso_base_app]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionRightUnit

/-! ## BimoduleCompositionLeftUnit（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionLeftUnit.lean） -/

/-! # 全導来bimodule合成の左単位と解像度に関する自然性

## 概要
全導来bimodule合成の左単位と解像度に関する自然性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionLeftUnitComputation.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionLeftUnit
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

def derivedBimoduleLeftUnitFunctor (hC : localHomKFlat A C) :
    DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B C :=
  derivedBimoduleComposeFunctor A B B C hC ⋙
    (CategoryTheory.evaluation (DerivedBimoduleCategory A B B) (DerivedBimoduleCategory A B C)).obj
      ((bimoduleToDerived A B B).obj (rightKFlatDiagonal A B).obj)

def derivedBimoduleLeftUnitResolutionIso (hC : localHomKFlat A C) (Q : BimoduleCategory A B C)
    (R : RightKFlatBimoduleCategory A B C) (q : R.obj ⟶ Q)
    (hq : BimoduleCategory.quasiIso A B C q) :
    (derivedBimoduleLeftUnitFunctor A B C hC).obj ((bimoduleToDerived A B C).obj Q) ≅
      (bimoduleToDerived A B C).obj Q :=
  (derivedBimoduleComposeResolutionComputation A B B C hC Q R q hq).app
      ((bimoduleToDerived A B B).obj (rightKFlatDiagonal A B).obj) ≪≫
    (bimoduleToDerived A B C).mapIso
      (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C R.obj)) ≪≫
    bimoduleDerivedIso A B C q hq

lemma derivedBimoduleLeftUnitResolutionIso_naturality (hC : localHomKFlat A C)
    {Q Q' : BimoduleCategory A B C} (R S : RightKFlatBimoduleCategory A B C)
    (q : R.obj ⟶ Q) (r : S.obj ⟶ Q')
    (hq : BimoduleCategory.quasiIso A B C q) (hr : BimoduleCategory.quasiIso A B C r)
    (f : Q ⟶ Q') (g : R ⟶ S)
    (h : (bimoduleToDerived A B C).map q ≫ (bimoduleToDerived A B C).map f =
      (bimoduleToDerived A B C).map g.hom ≫ (bimoduleToDerived A B C).map r) :
    (derivedBimoduleLeftUnitFunctor A B C hC).map ((bimoduleToDerived A B C).map f) ≫
        (derivedBimoduleLeftUnitResolutionIso A B C hC Q' S r hr).hom =
      (derivedBimoduleLeftUnitResolutionIso A B C hC Q R q hq).hom ≫
        (bimoduleToDerived A B C).map f := by
  let Δ := (bimoduleToDerived A B B).obj (rightKFlatDiagonal A B).obj
  let k := (derivedComposeWithMap A B B C R.property S.property g.hom).app Δ
  let c := (bimoduleToDerived A B C).map
    (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C S.obj)).hom
  let d := (bimoduleToDerived A B C).map r
  have hc := NatTrans.congr_app
    (derivedBimoduleComposeResolutionComputation_naturality A B B C hC R S q r hq hr f g h) Δ
  simp only [NatTrans.comp_app] at hc
  have hu : k ≫ c = (bimoduleToDerived A B C).map
      (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C R.obj)).hom ≫
        (bimoduleToDerived A B C).map g.hom := by
    change (derivedComposeWithMap A B B C R.property S.property g.hom).app
      ((bimoduleToDerived A B B).obj (rightKFlatDiagonal A B).obj) ≫ _ = _
    rw [derivedComposeWithMap_base_app, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp]
    exact congrArg (bimoduleToDerived A B C).map (leftBimoduleUnitIso_naturality A B C g.hom)
  change ((derivedBimoduleComposeFunctor A B B C hC).map
      ((bimoduleToDerived A B C).map f)).app Δ ≫
      ((derivedBimoduleComposeResolutionComputation A B B C hC Q' S r hr).hom.app Δ ≫
        (c ≫ d)) =
    ((derivedBimoduleComposeResolutionComputation A B B C hC Q R q hq).hom.app Δ ≫
      ((bimoduleToDerived A B C).map
        (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C R.obj)).hom ≫
          (bimoduleToDerived A B C).map q)) ≫ (bimoduleToDerived A B C).map f
  simp only [← Category.assoc]
  rw [hc]
  simp only [Category.assoc]
  rw [← Category.assoc k c d, hu]
  simp only [Category.assoc]
  rw [← h]

def derivedBimoduleLeftUnitBaseIso (hC : localHomKFlat A C) (Q : BimoduleCategory A B C) :
    (derivedBimoduleLeftUnitFunctor A B C hC).obj ((bimoduleToDerived A B C).obj Q) ≅
      (bimoduleToDerived A B C).obj Q :=
  derivedBimoduleLeftUnitResolutionIso A B C hC Q (rightKFlatResolutionObj A B C hC Q)
    (bimoduleCanonicalSemifreeResolution A B C Q).π
    (bimoduleCanonicalSemifreeResolution A B C Q).quasiIso

lemma derivedBimoduleLeftUnitBaseIso_naturality (hC : localHomKFlat A C)
    {Q Q' : BimoduleCategory A B C} (f : Q ⟶ Q') :
    (derivedBimoduleLeftUnitFunctor A B C hC).map ((bimoduleToDerived A B C).map f) ≫
        (derivedBimoduleLeftUnitBaseIso A B C hC Q').hom =
      (derivedBimoduleLeftUnitBaseIso A B C hC Q).hom ≫ (bimoduleToDerived A B C).map f := by
  apply derivedBimoduleLeftUnitResolutionIso_naturality A B C hC
    (rightKFlatResolutionObj A B C hC Q) (rightKFlatResolutionObj A B C hC Q')
    _ _ _ _ f (rightKFlatReplacementMap A B C hC f)
  have h := rightKFlatGlobalAugmentation_naturality A B C hC f
  change (rightKFlatDerivedInclusion A B C).map
      ((rightKFlatToDerived A B C).map (rightKFlatReplacementMap A B C hC f)) ≫ _ = _ at h
  rw [rightKFlatDerivedInclusion_map_base] at h
  exact h.symm

def derivedBimoduleLeftUnitLocalizedIso (hC : localHomKFlat A C) :
    bimoduleToDerived A B C ⋙ derivedBimoduleLeftUnitFunctor A B C hC ≅ bimoduleToDerived A B C :=
  NatIso.ofComponents (derivedBimoduleLeftUnitBaseIso A B C hC)
    (fun f => derivedBimoduleLeftUnitBaseIso_naturality A B C hC f)

def derivedBimoduleLeftUnitIso (hC : localHomKFlat A C) :
    derivedBimoduleLeftUnitFunctor A B C hC ≅ 𝟭 (DerivedBimoduleCategory A B C) :=
  Localization.liftNatIso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (bimoduleToDerived A B C ⋙ derivedBimoduleLeftUnitFunctor A B C hC) (bimoduleToDerived A B C)
    (derivedBimoduleLeftUnitFunctor A B C hC) (𝟭 _) (derivedBimoduleLeftUnitLocalizedIso A B C hC)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionLeftUnit

/-! ## BimoduleCompositionLeftUnitComputation（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionLeftUnitComputation.lean） -/

/-! # 左単位のK-flat因子での計算と任意解像度による表示

## 概要
左単位のK-flat因子での計算と任意解像度による表示。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionTriangle.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionLeftUnitComputation
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

lemma derivedBimoduleLeftUnitIso_base_app (hC : localHomKFlat A C) (Q : BimoduleCategory A B C) :
    (derivedBimoduleLeftUnitIso A B C hC).hom.app ((bimoduleToDerived A B C).obj Q) =
      (derivedBimoduleLeftUnitBaseIso A B C hC Q).hom := by
  have h := Localization.liftNatTrans_app (bimoduleToDerived A B C)
    (BimoduleCategory.quasiIso A B C)
    (bimoduleToDerived A B C ⋙ derivedBimoduleLeftUnitFunctor A B C hC) (bimoduleToDerived A B C)
    (derivedBimoduleLeftUnitFunctor A B C hC) (𝟭 _)
    (derivedBimoduleLeftUnitLocalizedIso A B C hC).hom Q
  change (derivedBimoduleLeftUnitIso A B C hC).hom.app
      ((bimoduleToDerived A B C).obj Q) =
    𝟙 _ ≫ (derivedBimoduleLeftUnitBaseIso A B C hC Q).hom ≫ 𝟙 _ at h
  simpa only [Category.id_comp, Category.comp_id] using h

lemma derivedBimoduleLeftUnitResolutionIso_self (hC : localHomKFlat A C)
    (R : RightKFlatBimoduleCategory A B C) :
    (derivedBimoduleLeftUnitResolutionIso A B C hC R.obj R (𝟙 R.obj)
      ((BimoduleCategory.quasiIso A B C).id_mem R.obj)).hom =
    (derivedBimoduleComposeKFlatValueIso A B B C hC R (rightKFlatDiagonal A B).obj).hom ≫
      (bimoduleToDerived A B C).map
        (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C R.obj)).hom := by
  change ((derivedBimoduleComposeResolutionComputation A B B C hC R.obj R (𝟙 R.obj)
      ((BimoduleCategory.quasiIso A B C).id_mem R.obj)).hom.app
        ((bimoduleToDerived A B B).obj (rightKFlatDiagonal A B).obj)) ≫
      ((bimoduleToDerived A B C).map _ ≫ (bimoduleToDerived A B C).map (𝟙 R.obj)) = _
  rw [derivedBimoduleComposeResolutionComputation_self, CategoryTheory.Functor.map_id,
    Category.comp_id]
  rfl

lemma derivedBimoduleLeftUnitIso_kFlat_base_app (hC : localHomKFlat A C)
    (R : RightKFlatBimoduleCategory A B C) :
    (derivedBimoduleLeftUnitIso A B C hC).hom.app ((bimoduleToDerived A B C).obj R.obj) =
      (derivedBimoduleComposeKFlatValueIso A B B C hC R (rightKFlatDiagonal A B).obj).hom ≫
        (bimoduleToDerived A B C).map
          (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C R.obj)).hom := by
  rw [derivedBimoduleLeftUnitIso_base_app]
  have h := derivedBimoduleLeftUnitResolutionIso_naturality A B C hC
    (rightKFlatResolutionObj A B C hC R.obj) R
    (bimoduleCanonicalSemifreeResolution A B C R.obj).π (𝟙 R.obj)
    (bimoduleCanonicalSemifreeResolution A B C R.obj).quasiIso
    ((BimoduleCategory.quasiIso A B C).id_mem R.obj) (𝟙 R.obj)
    (rightKFlatAugmentation A B C hC R) (by
      rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
      rfl)
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at h
  exact h.symm.trans (derivedBimoduleLeftUnitResolutionIso_self A B C hC R)

lemma derivedBimoduleLeftUnitResolutionIso_fac (hC : localHomKFlat A C)
    (Q : BimoduleCategory A B C) (R : RightKFlatBimoduleCategory A B C)
    (q : R.obj ⟶ Q) (hq : BimoduleCategory.quasiIso A B C q) :
    (derivedBimoduleLeftUnitFunctor A B C hC).map ((bimoduleToDerived A B C).map q) ≫
        (derivedBimoduleLeftUnitResolutionIso A B C hC Q R q hq).hom =
      (derivedBimoduleComposeKFlatValueIso A B B C hC R (rightKFlatDiagonal A B).obj).hom ≫
        (bimoduleToDerived A B C).map
          (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C R.obj)).hom ≫
        (bimoduleToDerived A B C).map q := by
  have h := NatTrans.congr_app (derivedBimoduleComposeResolutionComputation_fac A B B C hC Q R q hq)
    ((bimoduleToDerived A B B).obj (rightKFlatDiagonal A B).obj)
  simp only [NatTrans.comp_app] at h
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun t => t ≫
      ((bimoduleToDerived A B C).map
        (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C R.obj)).hom ≫
          (bimoduleToDerived A B C).map q)) h)

/-- 左単位の自然同型は、任意の指定K-flat解像度から作った表示に一致する。 -/
lemma derivedBimoduleLeftUnitIso_resolution_app (hC : localHomKFlat A C)
    (Q : BimoduleCategory A B C) (R : RightKFlatBimoduleCategory A B C)
    (q : R.obj ⟶ Q) (hq : BimoduleCategory.quasiIso A B C q) :
    (derivedBimoduleLeftUnitIso A B C hC).hom.app ((bimoduleToDerived A B C).obj Q) =
      (derivedBimoduleLeftUnitResolutionIso A B C hC Q R q hq).hom := by
  apply (Iso.cancel_iso_hom_left
    ((derivedBimoduleLeftUnitFunctor A B C hC).mapIso (bimoduleDerivedIso A B C q hq)) _ _).1
  change (derivedBimoduleLeftUnitFunctor A B C hC).map ((bimoduleToDerived A B C).map q) ≫ _ =
    (derivedBimoduleLeftUnitFunctor A B C hC).map ((bimoduleToDerived A B C).map q) ≫ _
  rw [derivedBimoduleLeftUnitResolutionIso_fac]
  rw [(derivedBimoduleLeftUnitIso A B C hC).hom.naturality,
    derivedBimoduleLeftUnitIso_kFlat_base_app, Category.assoc]
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionLeftUnitComputation

/-! ## BimoduleCompositionPairResolution（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionPairResolution.lean） -/

/-! # 全導来合成の二因子を指定K-flat解像度で計算する比較

## 概要
全導来合成の二因子を指定K-flat解像度で計算する比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionAssociatorResolution.lean、
Derived/BimoduleCompositionPairNaturality.lean。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionPairResolution
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

/-- 二つの全導来合成関手の逐次適用を、指定解像度での逐次適用へ比較する。 -/
def derivedBimoduleComposePairResolutionIso (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r) :
    (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q) ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj R) ≅
      derivedComposeWith A B C E S.obj S.property ⋙
        derivedComposeWith A B E F T.obj T.property :=
  Functor.isoWhiskerRight (derivedBimoduleComposeResolutionComputation A B C E hE Q S q hq)
      ((derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj R)) ≪≫
    Functor.isoWhiskerLeft (derivedComposeWith A B C E S.obj S.property)
      (derivedBimoduleComposeResolutionComputation A B E F hF R T r hr)

/-- 合成された後因子の値を、二つの指定K-flat解像度の通常合成へ比較する。 -/
def derivedBimoduleComposeInnerResolutionIso (hF : localHomKFlat A F)
    (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r) :
    ((derivedBimoduleComposeFunctor A C E F hF).obj ((bimoduleToDerived A E F).obj R)).obj
        ((bimoduleToDerived A C E).obj Q) ≅
      (bimoduleToDerived A C F).obj (rightKFlatCompose A C E F S T).obj :=
  (derivedBimoduleComposeResolutionComputation A C E F hF R T r hr).app
      ((bimoduleToDerived A C E).obj Q) ≪≫
    ((derivedComposeWith A C E F T.obj T.property).mapIso
      (bimoduleDerivedIso A C E q hq)).symm

/-- 合成された後因子による全導来関手を、解像度の通常合成による関手へ比較する。 -/
def derivedBimoduleComposeNestedResolutionIso (hF : localHomKFlat A F)
    (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r) :
    (derivedBimoduleComposeFunctor A B C F hF).obj
        (((derivedBimoduleComposeFunctor A C E F hF).obj
          ((bimoduleToDerived A E F).obj R)).obj ((bimoduleToDerived A C E).obj Q)) ≅
      derivedComposeWith A B C F (rightKFlatCompose A C E F S T).obj
        (rightKFlatCompose A C E F S T).property :=
  (derivedBimoduleComposeFunctor A B C F hF).mapIso
      (derivedBimoduleComposeInnerResolutionIso A C E F hF Q R S T q r hq hr) ≪≫
    derivedBimoduleComposeKFlatIso A B C F hF (rightKFlatCompose A C E F S T)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionPairResolution

/-! ## BimoduleCompositionPairNaturality（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionPairNaturality.lean） -/

/-! # 二つの解像度比較squareに関する逐次導来合成の自然性

## 概要
二つの解像度比較squareに関する逐次導来合成の自然性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionInnerNaturality.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionPairNaturality
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

def derivedBimoduleComposePairMap (hE : localHomKFlat A E) (hF : localHomKFlat A F)
    {Q Q' : DerivedBimoduleCategory A C E} {R R' : DerivedBimoduleCategory A E F}
    (f : Q ⟶ Q') (g : R ⟶ R') :
    (derivedBimoduleComposeFunctor A B C E hE).obj Q ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj R ⟶
      (derivedBimoduleComposeFunctor A B C E hE).obj Q' ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj R' :=
  whiskerRight ((derivedBimoduleComposeFunctor A B C E hE).map f)
      ((derivedBimoduleComposeFunctor A B E F hF).obj R) ≫
    whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj Q')
      ((derivedBimoduleComposeFunctor A B E F hF).map g)

lemma derivedBimoduleComposePairResolutionIso_naturality
    (hE : localHomKFlat A E) (hF : localHomKFlat A F)
    {Q Q' : BimoduleCategory A C E} {R R' : BimoduleCategory A E F}
    (S S' : RightKFlatBimoduleCategory A C E) (T T' : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (q' : S'.obj ⟶ Q') (r : T.obj ⟶ R) (r' : T'.obj ⟶ R')
    (hq : BimoduleCategory.quasiIso A C E q) (hq' : BimoduleCategory.quasiIso A C E q')
    (hr : BimoduleCategory.quasiIso A E F r) (hr' : BimoduleCategory.quasiIso A E F r')
    (f : Q ⟶ Q') (g : R ⟶ R') (s : S ⟶ S') (t : T ⟶ T')
    (hs : (bimoduleToDerived A C E).map q ≫ (bimoduleToDerived A C E).map f =
      (bimoduleToDerived A C E).map s.hom ≫ (bimoduleToDerived A C E).map q')
    (ht : (bimoduleToDerived A E F).map r ≫ (bimoduleToDerived A E F).map g =
      (bimoduleToDerived A E F).map t.hom ≫ (bimoduleToDerived A E F).map r') :
    derivedBimoduleComposePairMap A B C E F hE hF
        ((bimoduleToDerived A C E).map f) ((bimoduleToDerived A E F).map g) ≫
      (derivedBimoduleComposePairResolutionIso A B C E F hE hF Q' R' S' T' q' r' hq' hr').hom =
    (derivedBimoduleComposePairResolutionIso A B C E F hE hF Q R S T q r hq hr).hom ≫
      (whiskerRight (derivedComposeWithMap A B C E S.property S'.property s.hom)
          (derivedComposeWith A B E F T.obj T.property) ≫
        whiskerLeft (derivedComposeWith A B C E S'.obj S'.property)
          (derivedComposeWithMap A B E F T.property T'.property t.hom)) := by
  have hqnat := derivedBimoduleComposeResolutionComputation_naturality
    A B C E hE S S' q q' hq hq' f s hs
  have hrnat := derivedBimoduleComposeResolutionComputation_naturality
    A B E F hF T T' r r' hr hr' g t ht
  ext P
  have hqP := NatTrans.congr_app hqnat P
  have hrP := NatTrans.congr_app hrnat
    ((derivedComposeWith A B C E S'.obj S'.property).obj P)
  simp only [NatTrans.comp_app] at hqP hrP
  have hx := ((derivedBimoduleComposeFunctor A B E F hF).map
    ((bimoduleToDerived A E F).map g)).naturality
      ((derivedBimoduleComposeResolutionComputation A B C E hE Q' S' q' hq').hom.app P)
  have hy := (derivedBimoduleComposeResolutionComputation A B E F hF R T r hr).hom.naturality
    ((derivedComposeWithMap A B C E S.property S'.property s.hom).app P)
  change (_ ≫ _) ≫ (_ ≫ _) = (_ ≫ _) ≫ (_ ≫ _)
  simp only [isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    Category.assoc]
  rw [← reassoc_of% hx]
  simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  rw [hqP, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [hrP]
  rw [reassoc_of% hy]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionPairNaturality

/-! ## BimoduleCompositionValueNaturality（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionValueNaturality.lean） -/

/-! # 導来合成の値の指定解像度計算と後因子の射の整合性

## 概要
導来合成の値の指定解像度計算と後因子の射の整合性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleLocal.lean。固定dg圏上の導来tensor・
Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionValueNaturality
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]

lemma derivedBimoduleComposeResolutionValueIso_naturality (hE : localHomKFlat A E)
    {Q Q' : BimoduleCategory A C E} (R S : RightKFlatBimoduleCategory A C E)
    (q : R.obj ⟶ Q) (s : S.obj ⟶ Q')
    (hq : BimoduleCategory.quasiIso A C E q) (hs : BimoduleCategory.quasiIso A C E s)
    (f : Q ⟶ Q') (r : R ⟶ S)
    (h : (bimoduleToDerived A C E).map q ≫ (bimoduleToDerived A C E).map f =
      (bimoduleToDerived A C E).map r.hom ≫ (bimoduleToDerived A C E).map s)
    (P : BimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map f)).app
        ((bimoduleToDerived A B C).obj P) ≫
      (derivedBimoduleComposeResolutionValueIso A B C E hE Q' S s hs P).hom =
    (derivedBimoduleComposeResolutionValueIso A B C E hE Q R q hq P).hom ≫
      (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) r.hom) := by
  have hn := NatTrans.congr_app
    (derivedBimoduleComposeResolutionComputation_naturality A B C E hE R S q s hq hs f r h)
    ((bimoduleToDerived A B C).obj P)
  simp only [NatTrans.comp_app] at hn
  dsimp only [derivedBimoduleComposeResolutionValueIso, Iso.trans_hom]
  simp only [Iso.app_hom]
  rw [← Category.assoc, hn, Category.assoc, derivedComposeWithMap_computation, ← Category.assoc]

lemma derivedBimoduleComposeKFlatValueIso_naturality (hE : localHomKFlat A E)
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') (P : BimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map g.hom)).app
        ((bimoduleToDerived A B C).obj P) ≫
      (derivedBimoduleComposeKFlatValueIso A B C E hE Q' P).hom =
    (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).hom ≫
      (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) g.hom) := by
  have h := NatTrans.congr_app (derivedBimoduleComposeKFlatIso_naturality A B C E hE g)
    ((bimoduleToDerived A B C).obj P)
  simp only [NatTrans.comp_app, derivedComposeWithMap_base_app] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionValueNaturality

/-! ## BimoduleCompositionInnerNaturality（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionInnerNaturality.lean） -/

/-! # 合成された後因子の解像度比較の自然性

## 概要
合成された後因子の解像度比較の自然性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionAssociatorNaturality.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionInnerNaturality
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w) (F : Type z)
  [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} C] [Small.{u} E] [Small.{u} F]

def derivedBimoduleComposeInnerMap (hF : localHomKFlat A F)
    {Q Q' : DerivedBimoduleCategory A C E} {R R' : DerivedBimoduleCategory A E F}
    (f : Q ⟶ Q') (g : R ⟶ R') :
    ((derivedBimoduleComposeFunctor A C E F hF).obj R).obj Q ⟶
      ((derivedBimoduleComposeFunctor A C E F hF).obj R').obj Q' :=
  ((derivedBimoduleComposeFunctor A C E F hF).obj R).map f ≫
    ((derivedBimoduleComposeFunctor A C E F hF).map g).app Q'

lemma derivedBimoduleComposeInnerResolutionIso_naturality
    (hF : localHomKFlat A F)
    {Q Q' : BimoduleCategory A C E} {R R' : BimoduleCategory A E F}
    (S S' : RightKFlatBimoduleCategory A C E) (T T' : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (q' : S'.obj ⟶ Q') (r : T.obj ⟶ R) (r' : T'.obj ⟶ R')
    (hq : BimoduleCategory.quasiIso A C E q) (hq' : BimoduleCategory.quasiIso A C E q')
    (hr : BimoduleCategory.quasiIso A E F r) (hr' : BimoduleCategory.quasiIso A E F r')
    (f : Q ⟶ Q') (g : R ⟶ R') (s : S ⟶ S') (t : T ⟶ T')
    (hs : (bimoduleToDerived A C E).map q ≫ (bimoduleToDerived A C E).map f =
      (bimoduleToDerived A C E).map s.hom ≫ (bimoduleToDerived A C E).map q')
    (ht : (bimoduleToDerived A E F).map r ≫ (bimoduleToDerived A E F).map g =
      (bimoduleToDerived A E F).map t.hom ≫ (bimoduleToDerived A E F).map r') :
    derivedBimoduleComposeInnerMap A C E F hF
        ((bimoduleToDerived A C E).map f) ((bimoduleToDerived A E F).map g) ≫
      (derivedBimoduleComposeInnerResolutionIso A C E F hF Q' R' S' T' q' r' hq' hr').hom =
    (derivedBimoduleComposeInnerResolutionIso A C E F hF Q R S T q r hq hr).hom ≫
      (bimoduleToDerived A C F).map (composeMap A C E F s.hom t.hom) := by
  let iq := bimoduleDerivedIso A C E q hq
  let iq' := bimoduleDerivedIso A C E q' hq'
  have hs' : (bimoduleToDerived A C E).map f ≫ iq'.inv =
      iq.inv ≫ (bimoduleToDerived A C E).map s.hom := by
    apply (Iso.cancel_iso_hom_left iq _ _).1
    change (bimoduleToDerived A C E).map q ≫ _ = _
    rw [← Category.assoc, hs]
    change (_ ≫ iq'.hom) ≫ iq'.inv = iq.hom ≫ (iq.inv ≫ _)
    simp only [Category.assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc, Category.comp_id]
  have ht' := NatTrans.congr_app
    (derivedBimoduleComposeResolutionComputation_naturality
      A C E F hF T T' r r' hr hr' g t ht) ((bimoduleToDerived A C E).obj Q')
  simp only [NatTrans.comp_app] at ht'
  have hc := (derivedBimoduleComposeResolutionComputation A C E F hF R T r hr).hom.naturality
    ((bimoduleToDerived A C E).map f)
  have hx := (derivedComposeWithMap A C E F T.property T'.property t.hom).naturality iq'.inv
  have hm : (derivedComposeWith A C E F T.obj T.property).map
        ((bimoduleToDerived A C E).map s.hom) ≫
      (derivedComposeWithMap A C E F T.property T'.property t.hom).app
        ((bimoduleToDerived A C E).obj S'.obj) =
      (bimoduleToDerived A C F).map (composeMap A C E F s.hom t.hom) := by
    rw [derivedComposeWith_map_base, derivedComposeWithMap_base_app,
      ← CategoryTheory.Functor.map_comp]
    congr 1
    have h := composeMap_comp A C E F s.hom (𝟙 S'.obj) (𝟙 T.obj) t.hom
    simpa only [Category.comp_id, Category.id_comp] using h.symm
  change (_ ≫ _) ≫
      ((derivedBimoduleComposeResolutionComputation A C E F hF R' T' r' hr').hom.app
          ((bimoduleToDerived A C E).obj Q') ≫
        (derivedComposeWith A C E F T'.obj T'.property).map iq'.inv) =
    ((derivedBimoduleComposeResolutionComputation A C E F hF R T r hr).hom.app
        ((bimoduleToDerived A C E).obj Q) ≫
      (derivedComposeWith A C E F T.obj T.property).map iq.inv) ≫ _
  simp only [Category.assoc]
  rw [reassoc_of% ht']
  simp only [← Category.assoc]
  rw [hc]
  simp only [Category.assoc]
  rw [← hx]
  simp only [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  rw [hs', CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [hm]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionInnerNaturality

/-! ## BimoduleCompositionAssociatorResolution（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionAssociatorResolution.lean） -/

/-! # 指定K-flat解像度による全導来合成の結合比較

## 概要
指定K-flat解像度による全導来合成の結合比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionAssociatorNaturality.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionAssociatorResolution
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

/-- 最初の導来変数全体に自然な結合比較。後二因子には指定した解像度を使う。 -/
def derivedBimoduleAssociatorResolutionIso (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r) :
    (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q) ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj R) ≅
      (derivedBimoduleComposeFunctor A B C F hF).obj
        (((derivedBimoduleComposeFunctor A C E F hF).obj
          ((bimoduleToDerived A E F).obj R)).obj ((bimoduleToDerived A C E).obj Q)) :=
  derivedBimoduleComposePairResolutionIso A B C E F hE hF Q R S T q r hq hr ≪≫
    rightKFlatDerivedAssociator A B C E F S T ≪≫
    (derivedBimoduleComposeNestedResolutionIso A B C E F hF Q R S T q r hq hr).symm

/-- 全導来結合比較を解像度で計算すると、既存K-flat結合比較の図式に戻る。 -/
lemma derivedBimoduleAssociatorResolutionIso_fac (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r) :
    (derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q R S T q r hq hr).hom ≫
        (derivedBimoduleComposeNestedResolutionIso A B C E F hF Q R S T q r hq hr).hom =
      (derivedBimoduleComposePairResolutionIso A B C E F hE hF Q R S T q r hq hr).hom ≫
        (rightKFlatDerivedAssociator A B C E F S T).hom := by
  change (_ ≫ (_ ≫ _)) ≫ _ = _
  simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma derivedBimoduleAssociatorResolutionIso_base_fac (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r)
    (P : BimoduleCategory A B C) :
    (derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q R S T q r hq hr).hom.app
        ((bimoduleToDerived A B C).obj P) ≫
      (derivedBimoduleComposeNestedResolutionIso A B C E F hF Q R S T q r hq hr).hom.app
        ((bimoduleToDerived A B C).obj P) =
    (derivedBimoduleComposePairResolutionIso A B C E F hE hF Q R S T q r hq hr).hom.app
        ((bimoduleToDerived A B C).obj P) ≫
      (bimoduleToDerived A B F).map
        (associatorIso A B C E F (BimoduleCategory.underlying A B C P)
          (BimoduleCategory.underlying A C E S.obj)
          (BimoduleCategory.underlying A E F T.obj)).hom := by
  have h := NatTrans.congr_app
    (derivedBimoduleAssociatorResolutionIso_fac A B C E F hE hF Q R S T q r hq hr)
    ((bimoduleToDerived A B C).obj P)
  simp only [NatTrans.comp_app, rightKFlatDerivedAssociator_base_app] at h
  exact h

/-- 後二因子の標準解像度を使った結合比較。選択独立性・後因子自然性は別途必要。 -/
def derivedBimoduleAssociatorBaseIso (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F) :
    (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q) ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj R) ≅
      (derivedBimoduleComposeFunctor A B C F hF).obj
        (((derivedBimoduleComposeFunctor A C E F hF).obj
          ((bimoduleToDerived A E F).obj R)).obj ((bimoduleToDerived A C E).obj Q)) :=
  derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q R
    (rightKFlatResolutionObj A C E hE Q) (rightKFlatResolutionObj A E F hF R)
    (bimoduleCanonicalSemifreeResolution A C E Q).π
    (bimoduleCanonicalSemifreeResolution A E F R).π
    (bimoduleCanonicalSemifreeResolution A C E Q).quasiIso
    (bimoduleCanonicalSemifreeResolution A E F R).quasiIso

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionAssociatorResolution

/-! ## BimoduleCompositionAssociatorNaturality（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionAssociatorNaturality.lean） -/

/-! # 解像度比較に関する全導来結合比較の自然性

## 概要
解像度比較に関する全導来結合比較の自然性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionAssociatorFunctors.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionAssociatorNaturality
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

lemma derivedBimoduleComposeNestedResolutionIso_naturality
    (hF : localHomKFlat A F)
    {Q Q' : BimoduleCategory A C E} {R R' : BimoduleCategory A E F}
    (S S' : RightKFlatBimoduleCategory A C E) (T T' : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (q' : S'.obj ⟶ Q') (r : T.obj ⟶ R) (r' : T'.obj ⟶ R')
    (hq : BimoduleCategory.quasiIso A C E q) (hq' : BimoduleCategory.quasiIso A C E q')
    (hr : BimoduleCategory.quasiIso A E F r) (hr' : BimoduleCategory.quasiIso A E F r')
    (f : Q ⟶ Q') (g : R ⟶ R') (s : S ⟶ S') (t : T ⟶ T')
    (hs : (bimoduleToDerived A C E).map q ≫ (bimoduleToDerived A C E).map f =
      (bimoduleToDerived A C E).map s.hom ≫ (bimoduleToDerived A C E).map q')
    (ht : (bimoduleToDerived A E F).map r ≫ (bimoduleToDerived A E F).map g =
      (bimoduleToDerived A E F).map t.hom ≫ (bimoduleToDerived A E F).map r') :
    (derivedBimoduleComposeFunctor A B C F hF).map
        (derivedBimoduleComposeInnerMap A C E F hF
          ((bimoduleToDerived A C E).map f) ((bimoduleToDerived A E F).map g)) ≫
      (derivedBimoduleComposeNestedResolutionIso A B C E F hF Q' R' S' T' q' r' hq' hr').hom =
    (derivedBimoduleComposeNestedResolutionIso A B C E F hF Q R S T q r hq hr).hom ≫
      derivedComposeWithMap A B C F
        (rightKFlatCompose A C E F S T).property (rightKFlatCompose A C E F S' T').property
        (composeMap A C E F s.hom t.hom) := by
  have h := derivedBimoduleComposeInnerResolutionIso_naturality
    A C E F hF S S' T T' q q' r r' hq hq' hr hr' f g s t hs ht
  have hk := derivedBimoduleComposeKFlatIso_naturality A B C F hF
    (show rightKFlatCompose A C E F S T ⟶ rightKFlatCompose A C E F S' T' from
      ⟨composeMap A C E F s.hom t.hom⟩)
  change _ ≫ ((derivedBimoduleComposeFunctor A B C F hF).map
      (derivedBimoduleComposeInnerResolutionIso A C E F hF Q' R' S' T' q' r' hq' hr').hom ≫ _) =
    ((derivedBimoduleComposeFunctor A B C F hF).map
      (derivedBimoduleComposeInnerResolutionIso A C E F hF Q R S T q r hq hr).hom ≫ _) ≫ _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, h,
    CategoryTheory.Functor.map_comp, Category.assoc, hk, ← Category.assoc]

lemma derivedBimoduleAssociatorResolutionIso_naturality
    (hE : localHomKFlat A E) (hF : localHomKFlat A F)
    {Q Q' : BimoduleCategory A C E} {R R' : BimoduleCategory A E F}
    (S S' : RightKFlatBimoduleCategory A C E) (T T' : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (q' : S'.obj ⟶ Q') (r : T.obj ⟶ R) (r' : T'.obj ⟶ R')
    (hq : BimoduleCategory.quasiIso A C E q) (hq' : BimoduleCategory.quasiIso A C E q')
    (hr : BimoduleCategory.quasiIso A E F r) (hr' : BimoduleCategory.quasiIso A E F r')
    (f : Q ⟶ Q') (g : R ⟶ R') (s : S ⟶ S') (t : T ⟶ T')
    (hs : (bimoduleToDerived A C E).map q ≫ (bimoduleToDerived A C E).map f =
      (bimoduleToDerived A C E).map s.hom ≫ (bimoduleToDerived A C E).map q')
    (ht : (bimoduleToDerived A E F).map r ≫ (bimoduleToDerived A E F).map g =
      (bimoduleToDerived A E F).map t.hom ≫ (bimoduleToDerived A E F).map r') :
    derivedBimoduleComposePairMap A B C E F hE hF
        ((bimoduleToDerived A C E).map f) ((bimoduleToDerived A E F).map g) ≫
      (derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q' R' S' T' q' r' hq' hr').hom =
    (derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q R S T q r hq hr).hom ≫
      (derivedBimoduleComposeFunctor A B C F hF).map
        (derivedBimoduleComposeInnerMap A C E F hF
          ((bimoduleToDerived A C E).map f) ((bimoduleToDerived A E F).map g)) := by
  have hp := derivedBimoduleComposePairResolutionIso_naturality
    A B C E F hE hF S S' T T' q q' r r' hq hq' hr hr' f g s t hs ht
  have hn := derivedBimoduleComposeNestedResolutionIso_naturality
    A B C E F hF S S' T T' q q' r r' hq hq' hr hr' f g s t hs ht
  have ha := derivedAssociatorIso_naturality A B C E F
    S.property S'.property T.property T'.property s.hom t.hom
  change _ ≫ (rightKFlatDerivedAssociator A B C E F S' T').hom =
    (rightKFlatDerivedAssociator A B C E F S T).hom ≫ _ at ha
  apply (Iso.cancel_iso_hom_right _ _
    (derivedBimoduleComposeNestedResolutionIso A B C E F hF Q' R' S' T' q' r' hq' hr')).1
  simp only [Category.assoc]
  rw [derivedBimoduleAssociatorResolutionIso_fac]
  rw [← Category.assoc, hp]
  simp only [Category.assoc] at ha ⊢
  rw [ha]
  rw [hn]
  simp only [← Category.assoc]
  rw [derivedBimoduleAssociatorResolutionIso_fac]

lemma derivedBimoduleAssociatorBaseIso_naturality (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) {Q Q' : BimoduleCategory A C E}
    {R R' : BimoduleCategory A E F} (f : Q ⟶ Q') (g : R ⟶ R') :
    derivedBimoduleComposePairMap A B C E F hE hF
        ((bimoduleToDerived A C E).map f) ((bimoduleToDerived A E F).map g) ≫
      (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q' R').hom =
    (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R).hom ≫
      (derivedBimoduleComposeFunctor A B C F hF).map
        (derivedBimoduleComposeInnerMap A C E F hF
          ((bimoduleToDerived A C E).map f) ((bimoduleToDerived A E F).map g)) := by
  apply derivedBimoduleAssociatorResolutionIso_naturality A B C E F hE hF
    (rightKFlatResolutionObj A C E hE Q) (rightKFlatResolutionObj A C E hE Q')
    (rightKFlatResolutionObj A E F hF R) (rightKFlatResolutionObj A E F hF R')
    _ _ _ _ _ _ _ _ f g
    (rightKFlatReplacementMap A C E hE f) (rightKFlatReplacementMap A E F hF g)
  · have h := rightKFlatGlobalAugmentation_naturality A C E hE f
    change (rightKFlatDerivedInclusion A C E).map
      ((rightKFlatToDerived A C E).map (rightKFlatReplacementMap A C E hE f)) ≫ _ = _ at h
    rw [rightKFlatDerivedInclusion_map_base] at h
    exact h.symm
  · have h := rightKFlatGlobalAugmentation_naturality A E F hF g
    change (rightKFlatDerivedInclusion A E F).map
      ((rightKFlatToDerived A E F).map (rightKFlatReplacementMap A E F hF g)) ≫ _ = _ at h
    rw [rightKFlatDerivedInclusion_map_base] at h
    exact h.symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionAssociatorNaturality

/-! ## BimoduleCompositionAssociatorFunctors（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionAssociatorFunctors.lean） -/

/-! # 全導来結合比較の両辺を束ねる関手族

## 概要
全導来結合比較の両辺を束ねる関手族。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionAssociator.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionAssociatorFunctors
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

def derivedBimoduleAssociatorSource (hE : localHomKFlat A E) (hF : localHomKFlat A F) :
    DerivedBimoduleCategory A E F ⥤
      (DerivedBimoduleCategory A C E ⥤
        (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B F)) :=
  derivedBimoduleComposeFunctor A B E F hF ⋙
    whiskeringRight (DerivedBimoduleCategory A B C) (DerivedBimoduleCategory A B E)
      (DerivedBimoduleCategory A B F) ⋙
    (whiskeringLeft (DerivedBimoduleCategory A C E)
      (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E)
      (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B F)).obj
        (derivedBimoduleComposeFunctor A B C E hE)

def derivedBimoduleAssociatorTarget (hF : localHomKFlat A F) :
    DerivedBimoduleCategory A E F ⥤
      (DerivedBimoduleCategory A C E ⥤
        (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B F)) :=
  derivedBimoduleComposeFunctor A C E F hF ⋙
    (whiskeringRight (DerivedBimoduleCategory A C E) (DerivedBimoduleCategory A C F)
      (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B F)).obj
        (derivedBimoduleComposeFunctor A B C F hF)

/-- 後の因子を固定し、中間因子の閉零対象上で束ねた結合比較。 -/
def derivedBimoduleAssociatorMiddleBaseIso (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (R : BimoduleCategory A E F) :
    bimoduleToDerived A C E ⋙
        (derivedBimoduleAssociatorSource A B C E F hE hF).obj
          ((bimoduleToDerived A E F).obj R) ≅
      bimoduleToDerived A C E ⋙
        (derivedBimoduleAssociatorTarget A B C E F hF).obj
          ((bimoduleToDerived A E F).obj R) :=
  NatIso.ofComponents (fun Q => derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R)
    (fun {Q Q'} f => by
      change whiskerRight
          ((derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map f))
          ((derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj R)) ≫
        (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q' R).hom =
        (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R).hom ≫
          (derivedBimoduleComposeFunctor A B C F hF).map
            (((derivedBimoduleComposeFunctor A C E F hF).obj
              ((bimoduleToDerived A E F).obj R)).map ((bimoduleToDerived A C E).map f))
      have h := derivedBimoduleAssociatorBaseIso_naturality A B C E F hE hF f (𝟙 R)
      simpa only [derivedBimoduleComposePairMap, derivedBimoduleComposeInnerMap,
        CategoryTheory.Functor.map_id, whiskerLeft_id', Category.comp_id, NatTrans.id_app]
        using h)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionAssociatorFunctors

/-! ## BimoduleCompositionAssociator（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleCompositionAssociator.lean） -/

/-! # 全三因子に自然な導来bimodule合成の結合自然同型

## 概要
全三因子に自然な導来bimodule合成の結合自然同型。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/
BimoduleCompositionAssociatorIndependence.lean。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleCompositionAssociator
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

def derivedBimoduleAssociatorMiddleIso (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (R : BimoduleCategory A E F) :
    (derivedBimoduleAssociatorSource A B C E F hE hF).obj ((bimoduleToDerived A E F).obj R) ≅
      (derivedBimoduleAssociatorTarget A B C E F hF).obj ((bimoduleToDerived A E F).obj R) :=
  Localization.liftNatIso (bimoduleToDerived A C E) (BimoduleCategory.quasiIso A C E)
    _ _ _ _ (derivedBimoduleAssociatorMiddleBaseIso A B C E F hE hF R)

lemma derivedBimoduleAssociatorMiddleIso_base_app (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F) :
    (derivedBimoduleAssociatorMiddleIso A B C E F hE hF R).hom.app
        ((bimoduleToDerived A C E).obj Q) =
      (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R).hom := by
  have h := Localization.liftNatTrans_app (bimoduleToDerived A C E)
    (BimoduleCategory.quasiIso A C E)
    (bimoduleToDerived A C E ⋙ (derivedBimoduleAssociatorSource A B C E F hE hF).obj
      ((bimoduleToDerived A E F).obj R))
    (bimoduleToDerived A C E ⋙ (derivedBimoduleAssociatorTarget A B C E F hF).obj
      ((bimoduleToDerived A E F).obj R))
    ((derivedBimoduleAssociatorSource A B C E F hE hF).obj ((bimoduleToDerived A E F).obj R))
    ((derivedBimoduleAssociatorTarget A B C E F hF).obj ((bimoduleToDerived A E F).obj R))
    (derivedBimoduleAssociatorMiddleBaseIso A B C E F hE hF R).hom Q
  change (derivedBimoduleAssociatorMiddleIso A B C E F hE hF R).hom.app
    ((bimoduleToDerived A C E).obj Q) =
      𝟙 _ ≫ (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R).hom ≫ 𝟙 _ at h
  simpa only [Category.id_comp, Category.comp_id] using h

lemma derivedBimoduleAssociatorMiddleIso_naturality (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) {R R' : BimoduleCategory A E F} (g : R ⟶ R') :
    (derivedBimoduleAssociatorSource A B C E F hE hF).map ((bimoduleToDerived A E F).map g) ≫
        (derivedBimoduleAssociatorMiddleIso A B C E F hE hF R').hom =
      (derivedBimoduleAssociatorMiddleIso A B C E F hE hF R).hom ≫
        (derivedBimoduleAssociatorTarget A B C E F hF).map ((bimoduleToDerived A E F).map g) := by
  apply bimoduleDerivedNatTrans_ext A C E
  intro Q
  simp only [NatTrans.comp_app, derivedBimoduleAssociatorMiddleIso_base_app]
  change whiskerLeft
      ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q))
      ((derivedBimoduleComposeFunctor A B E F hF).map ((bimoduleToDerived A E F).map g)) ≫
    (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R').hom =
    (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R).hom ≫
      (derivedBimoduleComposeFunctor A B C F hF).map
        (((derivedBimoduleComposeFunctor A C E F hF).map
          ((bimoduleToDerived A E F).map g)).app ((bimoduleToDerived A C E).obj Q))
  have h := derivedBimoduleAssociatorBaseIso_naturality A B C E F hE hF (𝟙 Q) g
  simpa only [derivedBimoduleComposePairMap, derivedBimoduleComposeInnerMap,
    CategoryTheory.Functor.map_id, whiskerRight_id', Category.id_comp] using h

def derivedBimoduleAssociatorOuterBaseIso (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) :
    bimoduleToDerived A E F ⋙ derivedBimoduleAssociatorSource A B C E F hE hF ≅
      bimoduleToDerived A E F ⋙ derivedBimoduleAssociatorTarget A B C E F hF :=
  NatIso.ofComponents (derivedBimoduleAssociatorMiddleIso A B C E F hE hF)
    (fun g => derivedBimoduleAssociatorMiddleIso_naturality A B C E F hE hF g)

/-- 全後因子を指定準同型で局所化した関手族間の結合自然同型。 -/
def derivedBimoduleAssociatorIso (hE : localHomKFlat A E) (hF : localHomKFlat A F) :
    derivedBimoduleAssociatorSource A B C E F hE hF ≅
      derivedBimoduleAssociatorTarget A B C E F hF :=
  Localization.liftNatIso (bimoduleToDerived A E F) (BimoduleCategory.quasiIso A E F)
    _ _ _ _ (derivedBimoduleAssociatorOuterBaseIso A B C E F hE hF)

lemma derivedBimoduleAssociatorIso_outer_base_app (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (R : BimoduleCategory A E F) :
    (derivedBimoduleAssociatorIso A B C E F hE hF).hom.app ((bimoduleToDerived A E F).obj R) =
      (derivedBimoduleAssociatorMiddleIso A B C E F hE hF R).hom := by
  have h := Localization.liftNatTrans_app (bimoduleToDerived A E F)
    (BimoduleCategory.quasiIso A E F)
    (bimoduleToDerived A E F ⋙ derivedBimoduleAssociatorSource A B C E F hE hF)
    (bimoduleToDerived A E F ⋙ derivedBimoduleAssociatorTarget A B C E F hF)
    (derivedBimoduleAssociatorSource A B C E F hE hF)
    (derivedBimoduleAssociatorTarget A B C E F hF)
    (derivedBimoduleAssociatorOuterBaseIso A B C E F hE hF).hom R
  change (derivedBimoduleAssociatorIso A B C E F hE hF).hom.app
    ((bimoduleToDerived A E F).obj R) =
      𝟙 _ ≫ (derivedBimoduleAssociatorMiddleIso A B C E F hE hF R).hom ≫ 𝟙 _ at h
  simpa only [Category.id_comp, Category.comp_id] using h

lemma derivedBimoduleAssociatorIso_base_app (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F) :
    (((derivedBimoduleAssociatorIso A B C E F hE hF).app
      ((bimoduleToDerived A E F).obj R)).app ((bimoduleToDerived A C E).obj Q)).hom =
      (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R).hom := by
  change ((derivedBimoduleAssociatorIso A B C E F hE hF).hom.app
    ((bimoduleToDerived A E F).obj R)).app ((bimoduleToDerived A C E).obj Q) = _
  rw [derivedBimoduleAssociatorIso_outer_base_app, derivedBimoduleAssociatorMiddleIso_base_app]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleCompositionAssociator

/-! ## BimoduleResolutionLift（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleResolutionLift.lean） -/

/-! # 標準bimodule解像度から任意の準同型への持ち上げ

## 概要
標準bimodule解像度から任意の準同型への持ち上げ。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/
BimoduleCompositionAssociatorIndependence.lean。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleResolutionLift
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

/-- 標的は射影的でなくてよい。持ち上げの三角形は全dg自然なホモトピーまで可換。 -/
def bimoduleCanonicalResolutionSourceLift {M N : BimoduleCategory A B C}
    (q : N ⟶ M) (hq : BimoduleCategory.quasiIso A B C q) :
    (bimoduleSourceProjectiveResolution A B C M).obj ⟶
      (rightModuleBimoduleEquivalence A B C).inverse.obj N :=
  Classical.choose (moduleHomotopicallyProjective_homotopy_lift
    A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (bimoduleSourceProjectiveResolution A B C M).projective
    ((rightModuleBimoduleEquivalence A B C).inverse.map q)
    ((rightModuleBimodule_inverse_quasiIso_iff A B C q).2 hq)
    (bimoduleSourceProjectiveResolution A B C M).π)

def bimoduleCanonicalResolutionLift {M N : BimoduleCategory A B C}
    (q : N ⟶ M) (hq : BimoduleCategory.quasiIso A B C q) :
    (bimoduleCanonicalSemifreeResolution A B C M).obj ⟶ N :=
  (rightModuleBimoduleEquivalence A B C).functor.map
      (bimoduleCanonicalResolutionSourceLift A B C q hq) ≫
    ((rightModuleBimoduleEquivalence A B C).counitIso.app N).hom

lemma bimoduleCanonicalResolutionLift_fac {M N : BimoduleCategory A B C}
    (q : N ⟶ M) (hq : BimoduleCategory.quasiIso A B C q) :
    (bimoduleToDerived A B C).map (bimoduleCanonicalResolutionLift A B C q hq) ≫
        (bimoduleToDerived A B C).map q =
      (bimoduleToDerived A B C).map (bimoduleCanonicalSemifreeResolution A B C M).π := by
  let H := rightModuleBimoduleEquivalence A B C
  let P := bimoduleSourceProjectiveResolution A B C M
  have hs := Classical.choose_spec (moduleHomotopicallyProjective_homotopy_lift
    A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ P.projective (H.inverse.map q)
    ((rightModuleBimodule_inverse_quasiIso_iff A B C q).2 hq) P.π)
  have hsK : (moduleToHomotopy A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ).map
      (bimoduleCanonicalResolutionSourceLift A B C q hq ≫ H.inverse.map q) =
        (moduleToHomotopy A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ).map P.π :=
    (moduleToHomotopy_map_eq_iff A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ _ _).2 hs
  have he := BimoduleSemifreeResolution.map_eq_of_source_homotopy _ _ hsK
  have hl : H.functor.map
        (bimoduleCanonicalResolutionSourceLift A B C q hq ≫ H.inverse.map q) ≫
        (H.counitIso.app M).hom = bimoduleCanonicalResolutionLift A B C q hq ≫ q := by
    change H.functor.map (_ ≫ _) ≫ (H.counitIso.app M).hom =
      (H.functor.map _ ≫ (H.counitIso.app N).hom) ≫ q
    rw [H.functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg (fun k => H.functor.map
      (bimoduleCanonicalResolutionSourceLift A B C q hq) ≫ k) (H.counitIso.hom.naturality q)
  have hh := congrArg (fun k => k ≫ (bimoduleToDerived A B C).map
    (H.counitIso.app M).hom) he
  rw [← CategoryTheory.Functor.map_comp, hl, ← CategoryTheory.Functor.map_comp] at hh
  exact ((bimoduleToDerived A B C).map_comp _ _).symm.trans hh

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleResolutionLift
