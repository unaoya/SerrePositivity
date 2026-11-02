module

public import SerrePositivity.DifferentialGraded.Derived.BimoduleComposition.Resolution
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensor
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
public import SerrePositivity.DifferentialGraded.Bimodule.Value
public import SerrePositivity.DifferentialGraded.Derived.KFlat
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtension
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# Derived.BimoduleMiddle.ModelIndependence

## 概要
中間圏比較のモデル計算、解像度独立性と自然な族をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## BimoduleResolutionLiftTensor（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleResolutionLiftTensor.lean） -/

/-! # 任意の準同型への標準解像度の持ち上げと相対tensor後の増大square

## 概要
任意の準同型への標準解像度の持ち上げと相対tensor後の増大square。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleResolutionLiftTensor
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E] (P : BimoduleCategory A B C)

/-- 任意の前因子と合成した後も、標準解像度の持ち上げの増大三角形は導来可換。 -/
lemma composeAfter_bimoduleCanonicalResolutionLift_fac {M N : BimoduleCategory A C E}
    (q : N ⟶ M) (hq : BimoduleCategory.quasiIso A C E q) :
    (bimoduleToDerived A B E).map ((composeAfter A B C E P).map
        (bimoduleCanonicalResolutionLift A C E q hq)) ≫
      (bimoduleToDerived A B E).map ((composeAfter A B C E P).map q) =
    (bimoduleToDerived A B E).map ((composeAfter A B C E P).map
      (bimoduleCanonicalSemifreeResolution A C E M).π) := by
  let H := rightModuleBimoduleEquivalence A C E
  let R := bimoduleSourceProjectiveResolution A C E M
  let T := composeAfter A B C E P ⋙ bimoduleToDerived A B E
  have hs := Classical.choose_spec (moduleHomotopicallyProjective_homotopy_lift
    A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ R.projective (H.inverse.map q)
    ((rightModuleBimodule_inverse_quasiIso_iff A C E q).2 hq) R.π)
  have hsK : (moduleToHomotopy A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ).map
      (bimoduleCanonicalResolutionSourceLift A C E q hq ≫ H.inverse.map q) =
    (moduleToHomotopy A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ).map R.π :=
    (moduleToHomotopy_map_eq_iff A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ _ _).2 hs
  have he := composeAfter_map_eq_of_source_homotopy A B C E P _ _ hsK
  change T.map (H.functor.map _) = T.map (H.functor.map _) at he
  have hl : H.functor.map
      (bimoduleCanonicalResolutionSourceLift A C E q hq ≫ H.inverse.map q) ≫
      (H.counitIso.app M).hom = bimoduleCanonicalResolutionLift A C E q hq ≫ q := by
    change H.functor.map (_ ≫ _) ≫ (H.counitIso.app M).hom =
      (H.functor.map _ ≫ (H.counitIso.app N).hom) ≫ q
    rw [H.functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg (fun k => H.functor.map
      (bimoduleCanonicalResolutionSourceLift A C E q hq) ≫ k) (H.counitIso.hom.naturality q)
  have hh := congrArg (fun k => k ≫ T.map (H.counitIso.app M).hom) he
  rw [← T.map_comp, hl, ← T.map_comp] at hh
  exact (T.map_comp _ _).symm.trans hh

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleResolutionLiftTensor

/-! ## BimoduleMiddleComparison（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleComparison.lean） -/

/-! # 中間圏の制限後に解像度を取る導来bimodule合成比較

## 概要
制限後のK-flat性を仮定せず、制限後に選んだ解像度の増大を通して比較射を構成する。
準同値の場合の可逆性・解像度独立性は後続の受入条件である。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleComparison
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)

/-- 制限後の解像度の増大と、全Hom自然な中間圏比較射の合成。 -/
def middleRestrictionResolvedMap (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E)
    (R : BimoduleCategory A D E)
    (q : R ⟶ BimoduleCategory.of A D E
      (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q))) :
    BimoduleCategory.of A B E (compose A B D E
      (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P))
      (BimoduleCategory.underlying A D E R)) ⟶
        BimoduleCategory.of A B E (compose A B C E (BimoduleCategory.underlying A B C P)
          (BimoduleCategory.underlying A C E Q)) :=
  composeMap A B D E (𝟙 (BimoduleCategory.of A B D
      (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)))) q ≫
    middleRestrictionComparisonMap A B C D E F
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q)

omit [Small.{u} E] in
/-- 厳密な増大squareに関する解像度計算射の整合性。 -/
lemma middleRestrictionResolvedMap_comp (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E)
    {R S : BimoduleCategory A D E}
    (r : S ⟶ BimoduleCategory.of A D E
      (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q))) (g : R ⟶ S) :
    composeMap A B D E (𝟙 (BimoduleCategory.of A B D
        (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)))) g ≫
      middleRestrictionResolvedMap A B C D E F P Q S r =
        middleRestrictionResolvedMap A B C D E F P Q R (g ≫ r) := by
  dsimp only [middleRestrictionResolvedMap]
  rw [← Category.assoc, ← composeMap_comp, Category.id_comp]

/-- 既存の導来合成を、制限後に選んだ右K-flat解像度で計算する同型。 -/
def middleRestrictionSourceComputation (hE : localHomKFlat A E)
    (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ BimoduleCategory.of A D E
      (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q)))
    (hq : BimoduleCategory.quasiIso A D E q) :
    ((derivedBimoduleComposeFunctor A B D E hE).obj
      ((bimoduleToDerived A D E).obj (BimoduleCategory.of A D E
        (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q))))).obj
      ((bimoduleToDerived A B D).obj (BimoduleCategory.of A B D
        (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)))) ≅
      (bimoduleToDerived A B E).obj (BimoduleCategory.of A B E (compose A B D E
        (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P))
        (BimoduleCategory.underlying A D E R.obj))) :=
  (derivedBimoduleComposeResolutionComputation A B D E hE _ R q hq).app _ ≪≫
    derivedComposeWithComputation A B D E R.obj R.property _

/-- 後因子のK-flatモデルと制限後の解像度を指定した、実際の導来合成間の比較射。 -/
def derivedMiddleRestrictionComparison (hE : localHomKFlat A E)
    (P : BimoduleCategory A B C) (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ BimoduleCategory.of A D E
      (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q.obj)))
    (hq : BimoduleCategory.quasiIso A D E q) :
    ((derivedBimoduleComposeFunctor A B D E hE).obj
      ((bimoduleToDerived A D E).obj (BimoduleCategory.of A D E
        (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q.obj))))).obj
      ((bimoduleToDerived A B D).obj (BimoduleCategory.of A B D
        (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)))) ⟶
      ((derivedBimoduleComposeFunctor A B C E hE).obj
        ((bimoduleToDerived A C E).obj Q.obj)).obj ((bimoduleToDerived A B C).obj P) :=
  (middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).hom ≫
    (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q) ≫
      (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).inv

/-- 制限後の既存の標準semifree解像度を使う比較。追加のK-flat仮定は不要。 -/
def derivedMiddleRestrictionCanonicalComparison (hE : localHomKFlat A E)
    (P : BimoduleCategory A B C) (Q : RightKFlatBimoduleCategory A C E) :
    ((derivedBimoduleComposeFunctor A B D E hE).obj
      ((bimoduleToDerived A D E).obj (BimoduleCategory.of A D E
        (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q.obj))))).obj
      ((bimoduleToDerived A B D).obj (BimoduleCategory.of A B D
        (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)))) ⟶
      ((derivedBimoduleComposeFunctor A B C E hE).obj
        ((bimoduleToDerived A C E).obj Q.obj)).obj ((bimoduleToDerived A B C).obj P) :=
  derivedMiddleRestrictionComparison A B C D E F hE P Q
    (rightKFlatResolutionObj A D E hE _)
    (bimoduleCanonicalSemifreeResolution A D E _).π
    (bimoduleCanonicalSemifreeResolution A D E _).quasiIso

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleComparison

/-! ## BimoduleMiddleHomotopy（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleHomotopy.lean） -/

/-! # ホモトピー可換な増大squareに対する中間圏比較の計算射の整合性

## 概要
ホモトピー可換な増大squareに対する中間圏比較の計算射の整合性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleHomotopy
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)

/-- 増大射をsourceの全dg自然なホモトピーで替えても、比較の計算射の導来像は変わらない。 -/
lemma middleRestrictionResolvedMap_eq_of_source_homotopy
    (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E) (R : BimoduleCategory A D E)
    (q q' : R ⟶ BimoduleCategory.of A D E
      (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q)))
    (h : (moduleToHomotopy A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A D E).inverse.map q) =
      (moduleToHomotopy A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A D E).inverse.map q')) :
    (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q R q) =
      (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q R q') := by
  have he := composeAfter_map_eq_of_inverse_source_homotopy A B D E
    (BimoduleCategory.of A B D
      (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P))) q q' h
  dsimp only [middleRestrictionResolvedMap]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  exact congrArg (fun k => k ≫ (bimoduleToDerived A B E).map
    (middleRestrictionComparisonMap A B C D E F
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q))) he

/-- 解像度比較の増大squareはsourceの主Kで可換なら十分である。 -/
lemma middleRestrictionResolvedMap_comp_of_source_homotopy
    (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E)
    {R S : BimoduleCategory A D E}
    (q : R ⟶ BimoduleCategory.of A D E
      (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q)))
    (s : S ⟶ BimoduleCategory.of A D E
      (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q))) (r : R ⟶ S)
    (h : (moduleToHomotopy A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A D E).inverse.map (r ≫ s)) =
      (moduleToHomotopy A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A D E).inverse.map q)) :
    (bimoduleToDerived A B E).map (composeMap A B D E (𝟙 (BimoduleCategory.of A B D
        (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)))) r) ≫
      (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q S s) =
    (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q R q) := by
  rw [← CategoryTheory.Functor.map_comp, middleRestrictionResolvedMap_comp]
  exact middleRestrictionResolvedMap_eq_of_source_homotopy A B C D E F P Q R (r ≫ s) q h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleHomotopy

/-! ## BimoduleMiddleNaturality（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleNaturality.lean） -/

/-! # 解像度の増大squareに沿う中間圏比較の自然性

## 概要
解像度の増大squareに沿う中間圏比較の自然性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleNaturality
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)

/-- 両因子の射と厳密な増大squareに対する、解像度を使う実際の比較射の自然性。 -/
lemma middleRestrictionResolvedMap_naturality
    {P P' : BimoduleCategory A B C} {Q Q' : BimoduleCategory A C E}
    {R S : BimoduleCategory A D E} (f : P ⟶ P') (g : Q ⟶ Q') (r : R ⟶ S)
    (q : R ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q)
    (s : S ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q')
    (h : r ≫ s = q ≫ BimoduleCategory.middleRightRestrictionMap A C D E F g) :
    composeMap A B D E (BimoduleCategory.middleLeftRestrictionMap A B C D F f) r ≫
        middleRestrictionResolvedMap A B C D E F P' Q' S s =
      middleRestrictionResolvedMap A B C D E F P Q R q ≫ composeMap A B C E f g := by
  dsimp only [middleRestrictionResolvedMap]
  rw [← Category.assoc, ← composeMap_comp, Category.comp_id, h]
  have hc := composeMap_comp A B D E
    (𝟙 ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P))
    (BimoduleCategory.middleLeftRestrictionMap A B C D F f) q
    (BimoduleCategory.middleRightRestrictionMap A C D E F g)
  simp only [Category.id_comp] at hc
  rw [hc, Category.assoc, middleRestrictionComparisonMap_naturality, ← Category.assoc]
  rfl

/-- 後因子の指定モデルと増大を固定した、前因子の閉零圏上の比較自然変換。 -/
def middleRestrictionResolvedNatTrans (Q : BimoduleCategory A C E)
    (R : BimoduleCategory A D E)
    (q : R ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q) :
    BimoduleCategory.middleLeftRestrictionFunctor A B C D F ⋙ composeWith A B D E R ⟶
      composeWith A B C E Q where
  app P := middleRestrictionResolvedMap A B C D E F P Q R q
  naturality {P P'} f := by
    have h := middleRestrictionResolvedMap_naturality A B C D E F f (𝟙 Q) (𝟙 R) q q (by
      rw [Category.id_comp]
      exact (Category.comp_id q).symm.trans
        ((congrArg (fun k => q ≫ k)
          ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).map_id Q)).symm))
    exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleNaturality

/-! ## BimoduleMiddleCalculation（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleCalculation.lean） -/

/-! # 実際の導来中間比較から通常のモデル計算射を回復する

## 概要
実際の導来中間比較から通常のモデル計算射を回復する。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleCalculation
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (P : BimoduleCategory A B C)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A D E)
  (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

/-- source計算の逆とtarget計算で挟むと、既存の通常の解像度比較射を局所化した射になる。 -/
lemma derivedMiddleRestrictionComparison_calculation :
    (middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).inv ≫
      derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq ≫
      (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).hom =
    (bimoduleToDerived A B E).map
      (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q) := by
  unfold derivedMiddleRestrictionComparison
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleCalculation

/-! ## BimoduleMiddleComparisonFamily（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleComparisonFamily.lean） -/

/-! # 指定解像度による導来中間圏比較の前因子に関する自然変換

## 概要
指定解像度による導来中間圏比較の前因子に関する自然変換。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleComparisonFamily
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)

def middleDerivedSourceFamily : BimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E :=
  BimoduleCategory.middleLeftRestrictionFunctor A B C D F ⋙ bimoduleToDerived A B D ⋙
    (derivedBimoduleComposeFunctor A B D E hE).obj
      ((bimoduleToDerived A D E).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj))

def middleDerivedTargetFamily : BimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E :=
  bimoduleToDerived A B C ⋙
    (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj)

variable (R : RightKFlatBimoduleCategory A D E)
  (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

/-- sourceの計算同型を、既存の導来合成計算の自然同型から構成する。 -/
def middleDerivedSourceFamilyIso :
    middleDerivedSourceFamily A B C D E F hE Q ≅
      (BimoduleCategory.middleLeftRestrictionFunctor A B C D F ⋙ composeWith A B D E R.obj) ⋙
        bimoduleToDerived A B E :=
  Functor.isoWhiskerLeft (BimoduleCategory.middleLeftRestrictionFunctor A B C D F)
    (Functor.isoWhiskerLeft (bimoduleToDerived A B D)
      (derivedBimoduleComposeResolutionComputation A B D E hE _ R q hq) ≪≫
        eqToIso (derivedComposeWith_fac A B D E R.obj R.property)) ≪≫
    (Functor.associator _ _ _).symm

/-- targetの計算同型も既存のK-flat因子での計算を使う。 -/
def middleDerivedTargetFamilyIso :
    middleDerivedTargetFamily A B C E hE Q ≅ composeWith A B C E Q.obj ⋙ bimoduleToDerived A B E :=
  Functor.isoWhiskerLeft (bimoduleToDerived A B C)
    (derivedBimoduleComposeKFlatIso A B C E hE Q) ≪≫
      eqToIso (derivedComposeWith_fac A B C E Q.obj Q.property)

/-- 既存の実際の導来合成間の比較は、前因子の閉零圏上で自然。 -/
def derivedMiddleRestrictionComparisonFamily :
    middleDerivedSourceFamily A B C D E F hE Q ⟶ middleDerivedTargetFamily A B C E hE Q :=
  (middleDerivedSourceFamilyIso A B C D E F hE Q R q hq).hom ≫
    whiskerRight (middleRestrictionResolvedNatTrans A B C D E F Q.obj R.obj q)
      (bimoduleToDerived A B E) ≫
        (middleDerivedTargetFamilyIso A B C E hE Q).inv

lemma derivedMiddleRestrictionComparisonFamily_app (P : BimoduleCategory A B C) :
    (derivedMiddleRestrictionComparisonFamily A B C D E F hE Q R q hq).app P =
      derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq := by
  simp only [derivedMiddleRestrictionComparisonFamily, middleDerivedSourceFamilyIso,
    middleDerivedTargetFamilyIso, derivedMiddleRestrictionComparison,
    middleRestrictionSourceComputation, derivedBimoduleComposeKFlatValueIso,
    derivedComposeWithComputation, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, whiskerLeft_app,
    whiskerRight_app, Iso.symm_hom, Functor.associator_inv_app, Iso.app_hom, Iso.app_inv,
    eqToIso.hom, eqToIso.inv, eqToHom_refl, NatTrans.id_app, Category.comp_id, Category.id_comp,
    middleRestrictionResolvedNatTrans, Category.assoc]
  exact congrArg (fun k =>
    (derivedBimoduleComposeResolutionComputation A B D E hE
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj) R q hq).hom.app
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P)) ≫ k)
    (Category.id_comp ((bimoduleToDerived A B E).map
      (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q) ≫
        (derivedBimoduleComposeKFlatIso A B C E hE Q).inv.app
          ((bimoduleToDerived A B C).obj P))).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleComparisonFamily

/-! ## BimoduleMiddleComparisonLocalization（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleComparisonLocalization.lean） -/

/-! # 中間圏の導来合成比較を前因子の全導来圏へ降ろす

## 概要
中間圏の導来合成比較を前因子の全導来圏へ降ろす。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleComparisonLocalization
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)

lemma middleDerivedSourceFamily_inverts :
    (BimoduleCategory.quasiIso A B C).IsInvertedBy
      (middleDerivedSourceFamily A B C D E F hE Q) := by
  intro P P' f hf
  have hr : BimoduleCategory.quasiIso A B D
      (BimoduleCategory.middleLeftRestrictionMap A B C D F f) :=
    fun b d => hf b (F.obj d)
  have : IsIso ((bimoduleToDerived A B D).map
      (BimoduleCategory.middleLeftRestrictionMap A B C D F f)) :=
    bimoduleToDerived_inverts A B D _ hr
  exact ((derivedBimoduleComposeFunctor A B D E hE).obj
    ((bimoduleToDerived A D E).obj
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj))).map_isIso
      ((bimoduleToDerived A B D).map (BimoduleCategory.middleLeftRestrictionMap A B C D F f))

/-- 中間圏を制限してから導来合成する関手を、指定準同型の局所化へ延長する。 -/
def middleDerivedSourceLift : DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E :=
  bimoduleDerivedLift A B C (middleDerivedSourceFamily A B C D E F hE Q)
    (middleDerivedSourceFamily_inverts A B C D E F hE Q)

lemma middleDerivedSourceLift_fac :
    bimoduleToDerived A B C ⋙ middleDerivedSourceLift A B C D E F hE Q =
      middleDerivedSourceFamily A B C D E F hE Q :=
  bimoduleDerivedLift_fac A B C _ _

instance middleDerivedSourceLift_lifting :
    Localization.Lifting (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
      (middleDerivedSourceFamily A B C D E F hE Q) (middleDerivedSourceLift A B C D E F hE Q) :=
  ⟨eqToIso (middleDerivedSourceLift_fac A B C D E F hE Q)⟩

instance middleDerivedTargetFamily_lifting :
    Localization.Lifting (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
      (middleDerivedTargetFamily A B C E hE Q)
      ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj)) :=
  ⟨Iso.refl _⟩

/-- 前因子の全導来圏上の自然変換。後因子と制限後の解像度は指定されたものを使う。 -/
def derivedMiddleRestrictionComparisonLocalized (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D E q) :
    middleDerivedSourceLift A B C D E F hE Q ⟶
      (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj) :=
  Localization.liftNatTrans (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (middleDerivedSourceFamily A B C D E F hE Q) (middleDerivedTargetFamily A B C E hE Q)
    (middleDerivedSourceLift A B C D E F hE Q)
    ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj))
    (derivedMiddleRestrictionComparisonFamily A B C D E F hE Q R q hq)

/-- 局所化前の対象で、前項の実際の比較射を計算する式。 -/
lemma derivedMiddleRestrictionComparisonLocalized_app (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D E q) (P : BimoduleCategory A B C) :
    (derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q R q hq).app
        ((bimoduleToDerived A B C).obj P) =
      (Localization.Lifting.iso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
        (middleDerivedSourceFamily A B C D E F hE Q)
        (middleDerivedSourceLift A B C D E F hE Q)).hom.app P ≫
      derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq ≫
      (Localization.Lifting.iso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
        (middleDerivedTargetFamily A B C E hE Q)
        ((derivedBimoduleComposeFunctor A B C E hE).obj
          ((bimoduleToDerived A C E).obj Q.obj))).inv.app P := by
  have h := Localization.liftNatTrans_app (bimoduleToDerived A B C)
    (BimoduleCategory.quasiIso A B C) (middleDerivedSourceFamily A B C D E F hE Q)
    (middleDerivedTargetFamily A B C E hE Q) (middleDerivedSourceLift A B C D E F hE Q)
    ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj))
    (derivedMiddleRestrictionComparisonFamily A B C D E F hE Q R q hq) P
  rw [derivedMiddleRestrictionComparisonFamily_app] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleComparisonLocalization

/-! ## BimoduleMiddleIndependence（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleIndependence.lean） -/

/-! # 中間圏の導来比較射の解像度変更に関する整合性

## 概要
中間圏の導来比較射の解像度変更に関する整合性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleIndependence
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)
  (R S : RightKFlatBimoduleCategory A D E)
  (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (s : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q) (hs : BimoduleCategory.quasiIso A D E s)

/-- 増大squareと合成後の計算squareが導来可換なら、実際の比較射は一致する。 -/
lemma derivedMiddleRestrictionComparison_eq_of_squares (r : R ⟶ S)
    (h₀ : (bimoduleToDerived A D E).map q =
      (bimoduleToDerived A D E).map r.hom ≫ (bimoduleToDerived A D E).map s)
    (P : BimoduleCategory A B C)
    (h₁ : (bimoduleToDerived A B E).map (composeMap A B D E (𝟙 (BimoduleCategory.of A B D
        (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)))) r.hom) ≫
      (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q.obj S.obj s) =
      (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q)) :
    derivedMiddleRestrictionComparison A B C D E F hE P Q S s hs =
      derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq := by
  have hc : (middleRestrictionSourceComputation A B C D E F hE P Q.obj S s hs).hom =
      (middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).hom ≫
        (bimoduleToDerived A B E).map (composeMap A B D E (𝟙 (BimoduleCategory.of A B D
          (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)))) r.hom) :=
    derivedBimoduleComposeResolutionValueIso_change A B D E hE _ R S q s hq hs r h₀ _
  dsimp only [derivedMiddleRestrictionComparison]
  rw [hc]
  have he := congrArg (fun k =>
    (middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).hom ≫ k ≫
      (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).inv) h₁
  simpa only [Category.assoc] using he

/-- 増大squareが積dg圏表示の主Kで可換なら、指定解像度による導来比較は一致する。 -/
lemma derivedMiddleRestrictionComparison_eq_of_source_homotopy (r : R ⟶ S)
    (h : (moduleToHomotopy A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A D E).inverse.map (r.hom ≫ s)) =
      (moduleToHomotopy A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A D E).inverse.map q)) (P : BimoduleCategory A B C) :
    derivedMiddleRestrictionComparison A B C D E F hE P Q S s hs =
      derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq := by
  have h₀ := bimoduleDerived_map_eq_of_inverse_source_homotopy A D E (r.hom ≫ s) q h
  rw [CategoryTheory.Functor.map_comp] at h₀
  exact derivedMiddleRestrictionComparison_eq_of_squares A B C D E F hE Q R S q s hq hs r
    h₀.symm P (middleRestrictionResolvedMap_comp_of_source_homotopy A B C D E F
      P Q.obj q s r.hom h)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleIndependence

/-! ## BimoduleMiddleSecondFactor（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleSecondFactor.lean） -/

/-! # 増大squareから導く中間圏導来比較の後因子自然性

## 概要
増大squareから導く中間圏導来比較の後因子自然性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleSecondFactor
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)

lemma derivedMiddleRestrictionComparison_second_naturality_of_squares (hE : localHomKFlat A E)
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q')
    (R S : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (s : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q'.obj)
    (hq : BimoduleCategory.quasiIso A D E q) (hs : BimoduleCategory.quasiIso A D E s)
    (r : R ⟶ S)
    (h₀ : (bimoduleToDerived A D E).map q ≫
        (bimoduleToDerived A D E).map (BimoduleCategory.middleRightRestrictionMap A C D E F g.hom) =
      (bimoduleToDerived A D E).map r.hom ≫ (bimoduleToDerived A D E).map s)
    (P : BimoduleCategory A B C)
    (h₁ : (bimoduleToDerived A B E).map (composeMap A B D E (𝟙 (BimoduleCategory.of A B D
        (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)))) r.hom) ≫
      (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q'.obj S.obj s) =
      (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q) ≫
        (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) g.hom)) :
    ((derivedBimoduleComposeFunctor A B D E hE).map ((bimoduleToDerived A D E).map
        (BimoduleCategory.middleRightRestrictionMap A C D E F g.hom))).app
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P)) ≫
      derivedMiddleRestrictionComparison A B C D E F hE P Q' S s hs =
    derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq ≫
      ((derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map g.hom)).app
        ((bimoduleToDerived A B C).obj P) := by
  let P₀ := (BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P
  have hσ := derivedBimoduleComposeResolutionValueIso_naturality A B D E hE R S q s hq hs
    (BimoduleCategory.middleRightRestrictionMap A C D E F g.hom) r h₀ P₀
  have hτ := derivedBimoduleComposeKFlatValueIso_naturality A B C E hE g P
  apply (Iso.cancel_iso_hom_right _ _ (derivedBimoduleComposeKFlatValueIso A B C E hE Q' P)).1
  dsimp only [derivedMiddleRestrictionComparison]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hτ, Iso.inv_hom_id_assoc]
  change _ ≫ (middleRestrictionSourceComputation A B C D E F hE P Q'.obj S s hs).hom =
    (middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).hom ≫ _ at hσ
  have he := congrArg (fun k => k ≫ (bimoduleToDerived A B E).map
    (middleRestrictionResolvedMap A B C D E F P Q'.obj S.obj s)) hσ
  have hf := congrArg (fun k =>
    (middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).hom ≫ k) h₁
  exact (Category.assoc _ _ _).symm.trans
    (he.trans ((Category.assoc _ _ _).trans hf))

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleSecondFactor

/-! ## BimoduleMiddleKFlatIndependence（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleKFlatIndependence.lean） -/

/-! # 任意の右相対K-flat解像度による中間比較と既存標準比較の一致

## 概要
任意の右相対K-flat解像度による中間比較と既存標準比較の一致。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleKFlatIndependence
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)
  (R : RightKFlatBimoduleCategory A D E)
  (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

/-- semifree性を仮定せず、任意の右K-flat解像度による比較は標準比較に一致する。 -/
lemma derivedMiddleRestrictionComparison_kFlat_eq_canonical (P : BimoduleCategory A B C) :
    derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq =
      derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q := by
  let S := rightKFlatResolutionObj A D E hE
    ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  let s := (bimoduleCanonicalSemifreeResolution A D E
    ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)).π
  let r : S ⟶ R := ⟨bimoduleCanonicalResolutionLift A D E q hq⟩
  apply derivedMiddleRestrictionComparison_eq_of_squares A B C D E F hE Q S R s q
    (bimoduleCanonicalSemifreeResolution A D E _).quasiIso hq r
    (bimoduleCanonicalResolutionLift_fac A D E q hq).symm P
  let P₀ := (BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P
  have h := composeAfter_bimoduleCanonicalResolutionLift_fac A B D E P₀ q hq
  change (bimoduleToDerived A B E).map (composeMap A B D E (𝟙 P₀) r.hom) ≫
    (bimoduleToDerived A B E).map (composeMap A B D E (𝟙 P₀) q) =
    (bimoduleToDerived A B E).map (composeMap A B D E (𝟙 P₀) s) at h
  dsimp only [middleRestrictionResolvedMap]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    ← Category.assoc]
  exact congrArg (fun k => k ≫ (bimoduleToDerived A B E).map
    (middleRestrictionComparisonMap A B C D E F
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q.obj))) h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleKFlatIndependence

/-! ## BimoduleMiddleSemifreeIndependence（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleSemifreeIndependence.lean） -/

/-! # 制限後に選ぶsemifree解像度からの中間圏導来比較の独立性

## 概要
制限後に選ぶsemifree解像度からの中間圏導来比較の独立性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleSemifreeIndependence
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory

/-- 指定semifree解像度を、既存の局所Hom条件の下で右K-flat対象として読む。 -/
def BimoduleSemifreeResolution.toRightKFlat (A : Type u) [CommRing A]
    (D : Type z) [DGCategory A D] [Small.{u} D]
    (E : Type t) [DGCategory A E] [Small.{u} E] {M : BimoduleCategory A D E}
    (R : BimoduleSemifreeResolution A D E M) (hE : localHomKFlat A E) :
    BimoduleTensor.RightKFlatBimoduleCategory A D E :=
  ⟨R.obj, R.rightRelativeKFlat A D E hE⟩

namespace BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)
  (R S : BimoduleSemifreeResolution A D E
    ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj))

/-- 制限後の任意の二つのsemifree解像度による、実際の導来比較射の一致。 -/
lemma derivedMiddleRestrictionComparison_semifree_independent (P : BimoduleCategory A B C) :
    derivedMiddleRestrictionComparison A B C D E F hE P Q
        (S.toRightKFlat A D E hE) S.π S.quasiIso =
      derivedMiddleRestrictionComparison A B C D E F hE P Q
        (R.toRightKFlat A D E hE) R.π R.quasiIso := by
  let r : R.toRightKFlat A D E hE ⟶ S.toRightKFlat A D E hE :=
    ObjectProperty.homMk (R.comparison S)
  apply derivedMiddleRestrictionComparison_eq_of_squares A B C D E F hE Q
    (R.toRightKFlat A D E hE) (S.toRightKFlat A D E hE) R.π S.π R.quasiIso S.quasiIso r
    (R.comparison_fac S).symm P
  let P₀ := (BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P
  have hc := BimoduleSemifreeResolution.composeAfter_comparison_fac A B D E P₀ R S
  dsimp only [middleRestrictionResolvedMap]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ (bimoduleToDerived A B E).map
      (middleRestrictionComparisonMap A B C D E F
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q.obj))) hc)

lemma derivedMiddleRestrictionComparisonFamily_semifree_independent :
    derivedMiddleRestrictionComparisonFamily A B C D E F hE Q
        (S.toRightKFlat A D E hE) S.π S.quasiIso =
      derivedMiddleRestrictionComparisonFamily A B C D E F hE Q
        (R.toRightKFlat A D E hE) R.π R.quasiIso := by
  apply NatTrans.ext
  funext P
  rw [derivedMiddleRestrictionComparisonFamily_app, derivedMiddleRestrictionComparisonFamily_app]
  exact derivedMiddleRestrictionComparison_semifree_independent A B C D E F hE Q R S P

/-- 前因子の全導来圏上の自然変換も、選んだ制限後semifree解像度によらない。 -/
lemma derivedMiddleRestrictionComparisonLocalized_semifree_independent :
    derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q
        (S.toRightKFlat A D E hE) S.π S.quasiIso =
      derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q
        (R.toRightKFlat A D E hE) R.π R.quasiIso := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  rw [derivedMiddleRestrictionComparisonLocalized_app,
    derivedMiddleRestrictionComparisonLocalized_app,
    derivedMiddleRestrictionComparison_semifree_independent A B C D E F hE Q R S P]

omit S in
/-- 任意の制限後semifree解像度による射は、既存標準解像度を使う比較射と一致する。 -/
lemma derivedMiddleRestrictionComparison_semifree_eq_canonical (P : BimoduleCategory A B C) :
    derivedMiddleRestrictionComparison A B C D E F hE P Q
        (R.toRightKFlat A D E hE) R.π R.quasiIso =
      derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q :=
  (derivedMiddleRestrictionComparison_semifree_independent A B C D E F hE Q R
    (bimoduleCanonicalSemifreeResolution A D E _) P).symm

/-- 制限後の標準semifree解像度を使い、前因子の全導来圏上で自然な比較。 -/
def derivedMiddleRestrictionCanonicalLocalized :
    middleDerivedSourceLift A B C D E F hE Q ⟶
      (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj) :=
  derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q
    (rightKFlatResolutionObj A D E hE
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj))
    (bimoduleCanonicalSemifreeResolution A D E _).π
    (bimoduleCanonicalSemifreeResolution A D E _).quasiIso

omit S in
lemma derivedMiddleRestrictionComparisonLocalized_semifree_eq_canonical :
    derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q
        (R.toRightKFlat A D E hE) R.π R.quasiIso =
      derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q :=
  (derivedMiddleRestrictionComparisonLocalized_semifree_independent A B C D E F hE Q R
    (bimoduleCanonicalSemifreeResolution A D E _)).symm

end BimoduleTensor
end SerrePositivity.DifferentialGraded
end

end BimoduleMiddleSemifreeIndependence

/-! ## BimoduleMiddleSemifreeSecondFactor（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleSemifreeSecondFactor.lean） -/

/-! # 指定semifree解像度と標準解像度による中間圏導来比較の後因子自然性

## 概要
指定semifree解像度と標準解像度による中間圏導来比較の後因子自然性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleSemifreeSecondFactor
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)

lemma middleRestrictionResolvedMap_semifree_second_naturality
    (P : BimoduleCategory A B C) {Q Q' : BimoduleCategory A C E} (g : Q ⟶ Q')
    (R : BimoduleSemifreeResolution A D E
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q))
    (S : BimoduleSemifreeResolution A D E
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q')) :
    (bimoduleToDerived A B E).map (composeMap A B D E (𝟙 (BimoduleCategory.of A B D
        (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P))))
      (R.lift A D E S (BimoduleCategory.middleRightRestrictionMap A C D E F g))) ≫
      (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q' S.obj S.π) =
    (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q R.obj R.π) ≫
      (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) g) := by
  let P₀ := (BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P
  let T := bimoduleToDerived A B E
  have hc := BimoduleSemifreeResolution.composeAfter_lift_fac A D E B P₀ R S
    (BimoduleCategory.middleRightRestrictionMap A C D E F g)
  have hr : composeMap A B D E (𝟙 P₀)
        (BimoduleCategory.middleRightRestrictionMap A C D E F g) ≫
      middleRestrictionComparisonMap A B C D E F
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q') =
    middleRestrictionComparisonMap A B C D E F
        (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q) ≫
      composeMap A B C E (𝟙 P) g :=
    middleRestrictionComparisonMap_naturality A B C D E F (𝟙 P) g
  have hn := congrArg T.map hr
  rw [T.map_comp, T.map_comp] at hn
  dsimp only [middleRestrictionResolvedMap]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ T.map (middleRestrictionComparisonMap A B C D E F
      (BimoduleCategory.underlying A B C P) (BimoduleCategory.underlying A C E Q'))) hc).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => T.map (composeMap A B D E (𝟙 P₀) R.π) ≫ k) hn).trans
          (Category.assoc _ _ _).symm)))

lemma derivedMiddleRestrictionComparison_semifree_second_naturality (hE : localHomKFlat A E)
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q')
    (R : BimoduleSemifreeResolution A D E
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj))
    (S : BimoduleSemifreeResolution A D E
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q'.obj))
    (P : BimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A B D E hE).map ((bimoduleToDerived A D E).map
        (BimoduleCategory.middleRightRestrictionMap A C D E F g.hom))).app
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P)) ≫
      derivedMiddleRestrictionComparison A B C D E F hE P Q'
        (S.toRightKFlat A D E hE) S.π S.quasiIso =
    derivedMiddleRestrictionComparison A B C D E F hE P Q
        (R.toRightKFlat A D E hE) R.π R.quasiIso ≫
      ((derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map g.hom)).app
        ((bimoduleToDerived A B C).obj P) := by
  let r : R.toRightKFlat A D E hE ⟶ S.toRightKFlat A D E hE := ObjectProperty.homMk
    (R.lift A D E S (BimoduleCategory.middleRightRestrictionMap A C D E F g.hom))
  exact derivedMiddleRestrictionComparison_second_naturality_of_squares A B C D E F hE g
    (R.toRightKFlat A D E hE) (S.toRightKFlat A D E hE) R.π S.π R.quasiIso S.quasiIso r
    (R.lift_fac A D E S (BimoduleCategory.middleRightRestrictionMap A C D E F g.hom)).symm P
    (middleRestrictionResolvedMap_semifree_second_naturality A B C D E F P g.hom R S)

/-- 標準解像度による実際の導来比較は、任意の右K-flat後因子の射に対して自然。 -/
lemma derivedMiddleRestrictionCanonicalComparison_second_naturality (hE : localHomKFlat A E)
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') (P : BimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A B D E hE).map ((bimoduleToDerived A D E).map
        (BimoduleCategory.middleRightRestrictionMap A C D E F g.hom))).app
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P)) ≫
      derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q' =
    derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q ≫
      ((derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map g.hom)).app
        ((bimoduleToDerived A B C).obj P) :=
  derivedMiddleRestrictionComparison_semifree_second_naturality A B C D E F hE g
    (bimoduleCanonicalSemifreeResolution A D E _)
    (bimoduleCanonicalSemifreeResolution A D E _) P

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleSemifreeSecondFactor

/-! ## BimoduleMiddleSecondFamily（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleSecondFamily.lean） -/

/-! # 中間圏の標準導来比較の後因子自然性を自然変換の等式へ束ねる

## 概要
中間圏の標準導来比較の後因子自然性を自然変換の等式へ束ねる。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleSecondFamily
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E)

def middleDerivedSourceFamilyMap {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    middleDerivedSourceFamily A B C D E F hE Q ⟶ middleDerivedSourceFamily A B C D E F hE Q' :=
  whiskerLeft (BimoduleCategory.middleLeftRestrictionFunctor A B C D F)
    (whiskerLeft (bimoduleToDerived A B D)
      ((derivedBimoduleComposeFunctor A B D E hE).map ((bimoduleToDerived A D E).map
        (BimoduleCategory.middleRightRestrictionMap A C D E F g.hom))))

def middleDerivedTargetFamilyMap {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    middleDerivedTargetFamily A B C E hE Q ⟶ middleDerivedTargetFamily A B C E hE Q' :=
  whiskerLeft (bimoduleToDerived A B C)
    ((derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map g.hom))

def derivedMiddleRestrictionCanonicalFamily (Q : RightKFlatBimoduleCategory A C E) :
    middleDerivedSourceFamily A B C D E F hE Q ⟶ middleDerivedTargetFamily A B C E hE Q :=
  derivedMiddleRestrictionComparisonFamily A B C D E F hE Q
    (rightKFlatResolutionObj A D E hE
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj))
    (bimoduleCanonicalSemifreeResolution A D E _).π
    (bimoduleCanonicalSemifreeResolution A D E _).quasiIso

lemma derivedMiddleRestrictionCanonicalFamily_app (Q : RightKFlatBimoduleCategory A C E)
    (P : BimoduleCategory A B C) :
    (derivedMiddleRestrictionCanonicalFamily A B C D E F hE Q).app P =
      derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q :=
  derivedMiddleRestrictionComparisonFamily_app A B C D E F hE Q _ _ _ P

lemma derivedMiddleRestrictionCanonicalFamily_second_naturality
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    middleDerivedSourceFamilyMap A B C D E F hE g ≫
        derivedMiddleRestrictionCanonicalFamily A B C D E F hE Q' =
      derivedMiddleRestrictionCanonicalFamily A B C D E F hE Q ≫
        middleDerivedTargetFamilyMap A B C E hE g := by
  apply NatTrans.ext
  funext P
  simp only [NatTrans.comp_app, derivedMiddleRestrictionCanonicalFamily_app]
  exact derivedMiddleRestrictionCanonicalComparison_second_naturality A B C D E F hE g P

/-- 後因子の射を、前因子の全導来圏上のsource関手族の間の自然変換へ降ろす。 -/
def middleDerivedSourceLiftMap {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    middleDerivedSourceLift A B C D E F hE Q ⟶ middleDerivedSourceLift A B C D E F hE Q' :=
  Localization.liftNatTrans (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (middleDerivedSourceFamily A B C D E F hE Q) (middleDerivedSourceFamily A B C D E F hE Q')
    (middleDerivedSourceLift A B C D E F hE Q) (middleDerivedSourceLift A B C D E F hE Q')
    (middleDerivedSourceFamilyMap A B C D E F hE g)

lemma middleDerivedTargetFamilyMap_lift {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    Localization.liftNatTrans (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
      (middleDerivedTargetFamily A B C E hE Q) (middleDerivedTargetFamily A B C E hE Q')
      ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj))
      ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q'.obj))
      (middleDerivedTargetFamilyMap A B C E hE g) =
    (derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map g.hom) := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  rw [Localization.liftNatTrans_app]
  change 𝟙 _ ≫
    ((derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map g.hom)).app
      ((bimoduleToDerived A B C).obj P) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

lemma derivedMiddleRestrictionCanonicalFamily_lift (Q : RightKFlatBimoduleCategory A C E) :
    Localization.liftNatTrans (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
      (middleDerivedSourceFamily A B C D E F hE Q) (middleDerivedTargetFamily A B C E hE Q)
      (middleDerivedSourceLift A B C D E F hE Q)
      ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj))
      (derivedMiddleRestrictionCanonicalFamily A B C D E F hE Q) =
        derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q := rfl

/-- 標準比較は、前因子の全導来圏上の自然変換としても後因子の射に自然。 -/
lemma derivedMiddleRestrictionCanonicalLocalized_second_naturality
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    middleDerivedSourceLiftMap A B C D E F hE g ≫
        derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q' =
      derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q ≫
        (derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map g.hom) := by
  have h := congrArg (fun τ => Localization.liftNatTrans (bimoduleToDerived A B C)
    (BimoduleCategory.quasiIso A B C) (middleDerivedSourceFamily A B C D E F hE Q)
    (middleDerivedTargetFamily A B C E hE Q') (middleDerivedSourceLift A B C D E F hE Q)
    ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q'.obj)) τ)
    (derivedMiddleRestrictionCanonicalFamily_second_naturality A B C D E F hE g)
  have hleft := Localization.comp_liftNatTrans (bimoduleToDerived A B C)
    (BimoduleCategory.quasiIso A B C) (middleDerivedSourceFamily A B C D E F hE Q)
    (middleDerivedSourceFamily A B C D E F hE Q') (middleDerivedTargetFamily A B C E hE Q')
    (middleDerivedSourceLift A B C D E F hE Q) (middleDerivedSourceLift A B C D E F hE Q')
    ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q'.obj))
    (middleDerivedSourceFamilyMap A B C D E F hE g)
    (derivedMiddleRestrictionCanonicalFamily A B C D E F hE Q')
  have hright := Localization.comp_liftNatTrans (bimoduleToDerived A B C)
    (BimoduleCategory.quasiIso A B C) (middleDerivedSourceFamily A B C D E F hE Q)
    (middleDerivedTargetFamily A B C E hE Q) (middleDerivedTargetFamily A B C E hE Q')
    (middleDerivedSourceLift A B C D E F hE Q)
    ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj))
    ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q'.obj))
    (derivedMiddleRestrictionCanonicalFamily A B C D E F hE Q)
    (middleDerivedTargetFamilyMap A B C E hE g)
  rw [derivedMiddleRestrictionCanonicalFamily_lift] at hleft
  rw [derivedMiddleRestrictionCanonicalFamily_lift, middleDerivedTargetFamilyMap_lift] at hright
  exact hleft.trans (h.trans hright.symm)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleSecondFamily

/-! ## BimoduleMiddleKFlatFamily（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleKFlatFamily.lean） -/

/-! # 中間圏比較のsource関手族と右K-flat後因子の準同型局所化への準備

## 概要
中間圏比較のsource関手族と右K-flat後因子の準同型局所化への準備。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleKFlatFamily
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E)

lemma middleDerivedSourceFamilyMap_id (Q : RightKFlatBimoduleCategory A C E) :
    middleDerivedSourceFamilyMap A B C D E F hE (𝟙 Q) = 𝟙 _ := by
  change whiskerLeft _ (whiskerLeft _ ((derivedBimoduleComposeFunctor A B D E hE).map
    ((bimoduleToDerived A D E).map
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).map (𝟙 Q.obj))))) = _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]
  rfl

lemma middleDerivedSourceFamilyMap_comp {Q Q' Q'' : RightKFlatBimoduleCategory A C E}
    (g : Q ⟶ Q') (k : Q' ⟶ Q'') :
    middleDerivedSourceFamilyMap A B C D E F hE (g ≫ k) =
      middleDerivedSourceFamilyMap A B C D E F hE g ≫
        middleDerivedSourceFamilyMap A B C D E F hE k := by
  change whiskerLeft _ (whiskerLeft _ ((derivedBimoduleComposeFunctor A B D E hE).map
    ((bimoduleToDerived A D E).map
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).map (g.hom ≫ k.hom))))) = _
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, whiskerLeft_comp, whiskerLeft_comp]
  rfl

lemma middleDerivedSourceLiftMap_id (Q : RightKFlatBimoduleCategory A C E) :
    middleDerivedSourceLiftMap A B C D E F hE (𝟙 Q) = 𝟙 _ := by
  unfold middleDerivedSourceLiftMap
  rw [middleDerivedSourceFamilyMap_id]
  exact Localization.liftNatTrans_id _ _ _ _

lemma middleDerivedSourceLiftMap_comp {Q Q' Q'' : RightKFlatBimoduleCategory A C E}
    (g : Q ⟶ Q') (k : Q' ⟶ Q'') :
    middleDerivedSourceLiftMap A B C D E F hE (g ≫ k) =
      middleDerivedSourceLiftMap A B C D E F hE g ≫
        middleDerivedSourceLiftMap A B C D E F hE k := by
  unfold middleDerivedSourceLiftMap
  rw [middleDerivedSourceFamilyMap_comp, Localization.comp_liftNatTrans]

/-- 後因子の右K-flat部分圏上で、前因子の全導来圏の関手へ値を取るsource関手族。 -/
def middleDerivedSourceKFlatFunctor : RightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) where
  obj Q := middleDerivedSourceLift A B C D E F hE Q
  map g := middleDerivedSourceLiftMap A B C D E F hE g
  map_id := middleDerivedSourceLiftMap_id A B C D E F hE
  map_comp := middleDerivedSourceLiftMap_comp A B C D E F hE

def middleDerivedTargetKFlatFunctor : RightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) :=
  rightKFlatInclusion A C E ⋙ bimoduleToDerived A C E ⋙ derivedBimoduleComposeFunctor A B C E hE

/-- 標準比較を右K-flat後因子の圏上の自然変換として束ねる。 -/
def middleDerivedKFlatComparison :
    middleDerivedSourceKFlatFunctor A B C D E F hE ⟶
      middleDerivedTargetKFlatFunctor A B C E hE where
  app Q := derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q
  naturality {_Q _Q'} g :=
    derivedMiddleRestrictionCanonicalLocalized_second_naturality A B C D E F hE g

lemma middleDerivedSourceKFlatFunctor_inverts :
    (rightKFlatQuasiIso A C E).IsInvertedBy (middleDerivedSourceKFlatFunctor A B C D E F hE) := by
  intro Q Q' g hg
  let f := BimoduleCategory.middleRightRestrictionMap A C D E F g.hom
  have hf : BimoduleCategory.quasiIso A D E f := by
    intro d e
    rw [BimoduleCategory.middleRightRestrictionMap_value_eval]
    exact hg (F.obj d) e
  let e := Functor.isoWhiskerLeft (BimoduleCategory.middleLeftRestrictionFunctor A B C D F)
    (Functor.isoWhiskerLeft (bimoduleToDerived A B D)
      ((derivedBimoduleComposeFunctor A B D E hE).mapIso (bimoduleDerivedIso A D E f hf)))
  have : IsIso (middleDerivedSourceFamilyMap A B C D E F hE g) := e.isIso_hom
  exact (Localization.liftNatIso (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (middleDerivedSourceFamily A B C D E F hE Q) (middleDerivedSourceFamily A B C D E F hE Q')
    (middleDerivedSourceLift A B C D E F hE Q) (middleDerivedSourceLift A B C D E F hE Q')
    (asIso (middleDerivedSourceFamilyMap A B C D E F hE g))).isIso_hom

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleKFlatFamily

/-! ## BimoduleMiddleFullComparison（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleMiddleFullComparison.lean） -/

/-! # 両因子の全導来bimodule圏上の中間dg圏比較自然変換

## 概要
両因子の全導来bimodule圏上の中間dg圏比較自然変換。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleMiddleFullComparison
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E)

/-- 後因子も指定準同型の局所化へ降ろしたsource関手族。 -/
def middleRightKFlatLocalizedSource : DerivedRightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) :=
  Localization.Construction.lift (middleDerivedSourceKFlatFunctor A B C D E F hE)
    (middleDerivedSourceKFlatFunctor_inverts A B C D E F hE)

lemma middleRightKFlatLocalizedSource_fac :
    rightKFlatToDerived A C E ⋙ middleRightKFlatLocalizedSource A B C D E F hE =
      middleDerivedSourceKFlatFunctor A B C D E F hE := Localization.Construction.fac _ _

instance middleRightKFlatLocalizedSource_lifting :
    Localization.Lifting (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
      (middleDerivedSourceKFlatFunctor A B C D E F hE)
      (middleRightKFlatLocalizedSource A B C D E F hE) :=
  ⟨eqToIso (middleRightKFlatLocalizedSource_fac A B C D E F hE)⟩

lemma middleRightKFlatLocalizedTarget_fac :
    rightKFlatToDerived A C E ⋙
        (rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE) =
      middleDerivedTargetKFlatFunctor A B C E hE := by
  rw [← Functor.assoc, rightKFlatDerivedInclusion_fac]
  rfl

instance middleRightKFlatLocalizedTarget_lifting :
    Localization.Lifting (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
      (middleDerivedTargetKFlatFunctor A B C E hE)
      (rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE) :=
  ⟨eqToIso (middleRightKFlatLocalizedTarget_fac A B C E hE)⟩

def middleRightKFlatLocalizedComparison :
    middleRightKFlatLocalizedSource A B C D E F hE ⟶
      rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE :=
  Localization.liftNatTrans (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
    (middleDerivedSourceKFlatFunctor A B C D E F hE) (middleDerivedTargetKFlatFunctor A B C E hE)
    (middleRightKFlatLocalizedSource A B C D E F hE)
    (rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE)
    (middleDerivedKFlatComparison A B C D E F hE)

lemma middleRightKFlatLocalizedComparison_app (Q : RightKFlatBimoduleCategory A C E) :
    (middleRightKFlatLocalizedComparison A B C D E F hE).app ((rightKFlatToDerived A C E).obj Q) =
      (Localization.Lifting.iso (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
        (middleDerivedSourceKFlatFunctor A B C D E F hE)
        (middleRightKFlatLocalizedSource A B C D E F hE)).hom.app Q ≫
      derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q ≫
      (Localization.Lifting.iso (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
        (middleDerivedTargetKFlatFunctor A B C E hE)
        (rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE)).inv.app Q :=
  Localization.liftNatTrans_app _ _ _ _ _ _ _ _

/-- 後因子の既存K-flat置換を通した、両変数の全導来圏上のsource。 -/
def middleFullDerivedSource : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E) :=
  derivedRightKFlatReplacement A C E hE ⋙ middleRightKFlatLocalizedSource A B C D E F hE

/-- 後因子の既存置換同値の余単位と導来合成との比較。 -/
def middleFullDerivedTargetIso :
    derivedRightKFlatReplacement A C E hE ⋙
        (rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE) ≅
      derivedBimoduleComposeFunctor A B C E hE :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rightKFlatReplacementCounitIso A C E hE)
      (derivedBimoduleComposeFunctor A B C E hE) ≪≫ Functor.leftUnitor _

/-- 中間圏の制限と導来合成の比較。両変数とも実際の全導来bimodule圏上で自然。 -/
def middleFullDerivedComparison :
    middleFullDerivedSource A B C D E F hE ⟶ derivedBimoduleComposeFunctor A B C E hE :=
  whiskerLeft (derivedRightKFlatReplacement A C E hE)
    (middleRightKFlatLocalizedComparison A B C D E F hE) ≫
      (middleFullDerivedTargetIso A B C E hE).hom

lemma middleFullDerivedComparison_app (Q : DerivedBimoduleCategory A C E) :
    (middleFullDerivedComparison A B C D E F hE).app Q =
      (middleRightKFlatLocalizedComparison A B C D E F hE).app
        ((derivedRightKFlatReplacement A C E hE).obj Q) ≫
          (middleFullDerivedTargetIso A B C E hE).hom.app Q := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleMiddleFullComparison

/-! ## BimoduleModuleEquivalence（旧 SerrePositivity/DifferentialGraded/Derived/BimoduleModuleEquivalence.lean） -/

/-! # 積dg圏上の右加群とbimoduleの主導来圏の比較

## 概要
積dg圏上の右加群とbimoduleの主導来圏の比較。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。固定dg圏上の導来tensor・Morita作用の基盤。
非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleModuleEquivalence
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]

/-- 閉零比較の逆を通して、積dg圏上の右加群の主導来圏へ送る。 -/
def bimoduleToModuleDerived :
    BimoduleCategory A B C ⥤ DerivedModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ :=
  (rightModuleBimoduleEquivalence A B C).inverse ⋙
    moduleToDerived A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ

lemma bimoduleToModuleDerived_inverts :
    (BimoduleCategory.quasiIso A B C).IsInvertedBy (bimoduleToModuleDerived A B C) := by
  intro M N f hf
  exact moduleToDerived_inverts A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ _
    ((rightModuleBimodule_inverse_quasiIso_iff A B C f).mpr hf)

/-- 閉零比較と準同型の一致から、同じ射のクラスの局所化である。 -/
instance bimoduleToModuleDerivedIsLocalization :
    (bimoduleToModuleDerived A B C).IsLocalization (BimoduleCategory.quasiIso A B C) := by
  let E := rightModuleBimoduleEquivalence A B C
  let Q := moduleToDerived A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
  apply Functor.IsLocalization.of_equivalence_source Q
    (moduleQuasiIso A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ)
    (bimoduleToModuleDerived A B C) (BimoduleCategory.quasiIso A B C) E
  · intro M N f hf
    exact (BimoduleCategory.quasiIso A B C).le_isoClosure _
      ((rightModuleBimoduleEquivalence_quasiIso_iff A B C f).mpr hf)
  · exact bimoduleToModuleDerived_inverts A B C
  · exact (Functor.associator E.functor E.inverse Q).symm ≪≫
      Functor.isoWhiskerRight E.unitIso.symm Q ≪≫ Functor.leftUnitor Q

/-- HomのK-flat性なしで、同じ値ごとの準同型を局所化した二つの表示を比較する。 -/
def rightModuleBimoduleDerivedEquivalence :
    DerivedModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ ≌ DerivedBimoduleCategory A B C :=
  Localization.uniq (bimoduleToModuleDerived A B C) (bimoduleToDerived A B C)
    (BimoduleCategory.quasiIso A B C)

def rightModuleBimoduleDerived_fac :
    bimoduleToModuleDerived A B C ⋙ (rightModuleBimoduleDerivedEquivalence A B C).functor ≅
      bimoduleToDerived A B C :=
  Localization.compUniqFunctor (bimoduleToModuleDerived A B C) (bimoduleToDerived A B C)
    (BimoduleCategory.quasiIso A B C)

def rightModuleBimoduleDerived_inverse_fac :
    bimoduleToDerived A B C ⋙ (rightModuleBimoduleDerivedEquivalence A B C).inverse ≅
      bimoduleToModuleDerived A B C :=
  Localization.compUniqInverse (bimoduleToModuleDerived A B C) (bimoduleToDerived A B C)
    (BimoduleCategory.quasiIso A B C)

end SerrePositivity.DifferentialGraded
end

end BimoduleModuleEquivalence
