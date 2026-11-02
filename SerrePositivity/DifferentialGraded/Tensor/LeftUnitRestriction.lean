module

public import SerrePositivity.DifferentialGraded.Bimodule.DiagonalRestriction
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions
public import SerrePositivity.DifferentialGraded.Tensor.Compose
public import SerrePositivity.DifferentialGraded.Tensor.Triple
public import SerrePositivity.DifferentialGraded.Tensor.Fubini
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import SerrePositivity.DifferentialGraded.Module.FunctorExtension
public import SerrePositivity.DifferentialGraded.Module.LeftEquivalence
public import SerrePositivity.DifferentialGraded.Module.LeftClosedMaps
public import SerrePositivity.DifferentialGraded.Module.Isomorphism

/-!
# Tensor.LeftUnitRestriction

## 概要
4 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## LeftUnitRestriction（旧 SerrePositivity/DifferentialGraded/Tensor/LeftUnitRestriction.lean） -/

/-! # 対角のHom比較と中間制限比較による左単位子の保存

## 概要
対角のHom比較と中間制限比較による左単位子の保存。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section LeftUnitRestriction
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] (F : DGFunctor A D B)

local notation "RP" P => Functor.obj
  (BimoduleCategory.middleRightRestrictionFunctor A B D C F) P
local notation "LD" => Functor.obj (BimoduleCategory.middleLeftRestrictionFunctor A B B D F)
  (BimoduleCategory.of A B B (Bimodule.diagonal A B))

/-- 対角比較と外側右制限比較を続けた射をcoend包含で計算する。 -/
@[reassoc]
lemma ι_leftUnitRestriction_comparison (P : BimoduleCategory A B C) (d x : D) (c : C) :
    BalancedTensor.ι A D ((BimoduleCategory.underlying A D C (RP P)).rightAt c)
        ((Bimodule.diagonal A D).leftAt d) x ≫
      composeValueMap A D D C (Bimodule.diagonalRestrictionMap A D B F) (𝟙 (RP P)) d c ≫
      (composeRightRestrictionValueIso A B D D C F
        (BimoduleCategory.underlying A B D LD) (BimoduleCategory.underlying A D C (RP P))
        d c).hom =
    (𝟙 ((BimoduleCategory.underlying A B C P).value (F.obj x) c) ⊗ₘ F.map d x) ≫
      BalancedTensor.ι A D ((BimoduleCategory.underlying A D C (RP P)).rightAt c)
        ((Bimodule.leftRestriction A B B D F (Bimodule.diagonal A B)).leftAt (F.obj d)) x := by
  have h₁ := ι_composeValueMap A D D C (Bimodule.diagonalRestrictionMap A D B F)
    (𝟙 (RP P)) d x c
  have h₂ := ι_composeRightRestrictionValueIso_hom A B D D C F
    (BimoduleCategory.underlying A B D LD) (BimoduleCategory.underlying A D C (RP P)) d c x
  have h := congrArg (fun k => k ≫ (composeRightRestrictionValueIso A B D D C F
    (BimoduleCategory.underlying A B D LD) (BimoduleCategory.underlying A D C (RP P))
    d c).hom) h₁
  simp only [Bimodule.diagonalRestrictionMap_value, CategoryTheory.Functor.map_id] at h
  refine (Category.assoc _ _ _).symm.trans (h.trans ?_)
  have h₂' := congrArg (fun k =>
    (𝟙 ((BimoduleCategory.underlying A B C P).value (F.obj x) c) ⊗ₘ F.map d x) ≫ k) h₂
  convert h₂' using 1 <;> rfl

/-- 対角比較・外側右制限・中間比較・左単位子を値の複体で照合する。 -/
lemma leftUnitRestriction_value (P : BimoduleCategory A B C) (d : D) (c : C) :
    composeValueMap A D D C (Bimodule.diagonalRestrictionMap A D B F) (𝟙 (RP P)) d c ≫
      (composeRightRestrictionValueIso A B D D C F
        (BimoduleCategory.underlying A B D LD) (BimoduleCategory.underlying A D C (RP P))
        d c).hom ≫
      middleRestrictionComparisonValue A B B D C F (Bimodule.diagonal A B)
        (BimoduleCategory.underlying A B C P) (F.obj d) c ≫
      (leftUnitValueIso A B C (BimoduleCategory.underlying A B C P) (F.obj d) c).hom =
    (leftUnitValueIso A D C (BimoduleCategory.underlying A D C (RP P)) d c).hom := by
  apply BalancedTensor.hom_ext
  intro x
  erw [ι_leftUnitRestriction_comparison_assoc A B D C F P d x c]
  erw [ι_middleRestrictionComparisonValue_assoc A B B D C F (Bimodule.diagonal A B)
    (BimoduleCategory.underlying A B C P) (F.obj d) c x]
  rw [ι_leftUnitValueIso_hom]
  erw [ι_leftUnitValueIso_hom A D C (BimoduleCategory.underlying A D C (RP P)) d x c]
  exact (BalancedTensor.rightAction_restrict A D B F
    ((BimoduleCategory.underlying A B C P).rightAt c) d x).symm

/-- 左単位子は対角のHom比較・外側右制限・中間比較と整合する。 -/
lemma leftUnitRestriction (P : BimoduleCategory A B C) :
    composeMap A D D C (Bimodule.diagonalRestrictionMap A D B F) (𝟙 (RP P)) ≫
      (composeRightRestrictionIso A B D D C F LD (RP P)).hom ≫
      (BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
        (middleRestrictionComparisonMap A B B D C F (Bimodule.diagonal A B)
          (BimoduleCategory.underlying A B C P)) ≫
      (BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
        (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom =
    (leftBimoduleUnitIso A D C (BimoduleCategory.underlying A D C (RP P))).hom := by
  apply BimoduleCategory.value_hom_ext A D C
  intro d c
  simp only [CategoryTheory.Functor.map_comp, composeMap_value_eval,
    composeRightRestrictionIso_hom_value]
  erw [BimoduleCategory.middleRightRestrictionMap_value_eval A B D C F
    (middleRestrictionComparisonMap A B B D C F (Bimodule.diagonal A B)
      (BimoduleCategory.underlying A B C P)) d c,
    BimoduleCategory.middleRightRestrictionMap_value_eval A B D C F
      (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom d c,
    middleRestrictionComparisonMap_value_eval,
    leftBimoduleUnitIso_hom_value, leftBimoduleUnitIso_hom_value]
  exact leftUnitRestriction_value A B D C F P d c

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end LeftUnitRestriction

/-! ## LeftUnitRestrictionAugmentation（旧 SerrePositivity/DifferentialGraded/Tensor/LeftUnitRestrictionAugmentation.lean） -/

/-! # 制限後の指定増大射による左単位squareの計算

## 概要
制限後の指定増大射による左単位squareの計算。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section LeftUnitRestrictionAugmentation
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] (F : DGFunctor A D B)
  (P : BimoduleCategory A B C) (R : BimoduleCategory A D C)

local notation "RP" => Functor.obj
  (BimoduleCategory.middleRightRestrictionFunctor A B D C F) P
local notation "LD" => Functor.obj (BimoduleCategory.middleLeftRestrictionFunctor A B B D F)
  (BimoduleCategory.of A B B (Bimodule.diagonal A B))
local notation "DD" => BimoduleCategory.of A D D (Bimodule.diagonal A D)
local notation "qD" => Bimodule.diagonalRestrictionMap A D B F

/-- 指定増大射は、対角比較および外側右制限比較と交換する。 -/
@[reassoc]
lemma leftUnitRestriction_augmentation_exchange (q : R ⟶ RP) :
    composeMap A D D C qD (𝟙 R) ≫
      (composeRightRestrictionIso A B D D C F LD R).hom ≫
      (BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
        (composeMap A B D C (𝟙 LD) q) =
    composeMap A D D C (𝟙 DD) q ≫ composeMap A D D C qD (𝟙 RP) ≫
      (composeRightRestrictionIso A B D D C F LD RP).hom := by
  have hn := composeRightRestrictionIso_naturality A B D D C F (𝟙 LD) q
  simp only [CategoryTheory.Functor.map_id] at hn
  have hx : composeMap A D D C qD (𝟙 R) ≫
      composeMap A D D C
        (𝟙 ((BimoduleCategory.pairedRestrictionFunctor A B B D D F F).obj
          (BimoduleCategory.of A B B (Bimodule.diagonal A B)))) q =
    composeMap A D D C (𝟙 DD) q ≫ composeMap A D D C qD (𝟙 RP) := by
    rw [← composeMap_comp, ← composeMap_comp, Category.comp_id, Category.id_comp,
      Category.comp_id, Category.id_comp]
  have h := congrArg (fun k => composeMap A D D C qD (𝟙 R) ≫ k) hn.symm
  have hh := congrArg (fun k => k ≫ (composeRightRestrictionIso A B D D C F LD RP).hom) hx
  exact h.trans ((Category.assoc _ _ _).symm.trans (hh.trans (Category.assoc _ _ _)))

/-- 任意の増大射の下で、左単位squareの出力は元の左単位子に増大を続けた射。 -/
lemma leftUnitRestriction_augmentation (q : R ⟶ RP) :
    composeMap A D D C qD (𝟙 R) ≫
      (composeRightRestrictionIso A B D D C F LD R).hom ≫
      (BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
        (composeMap A B D C (𝟙 LD) q ≫
          middleRestrictionComparisonMap A B B D C F (Bimodule.diagonal A B)
            (BimoduleCategory.underlying A B C P)) ≫
      (BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
        (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom =
    (leftBimoduleUnitIso A D C (BimoduleCategory.underlying A D C R)).hom ≫ q := by
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [leftUnitRestriction_augmentation_exchange_assoc A B D C F P R q,
    leftUnitRestriction A B D C F P]
  exact leftBimoduleUnitIso_naturality A D C q

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end LeftUnitRestrictionAugmentation

/-! ## RightUnitRestriction（旧 SerrePositivity/DifferentialGraded/Tensor/RightUnitRestriction.lean） -/

/-! # 対角のHom比較と中間制限比較による右単位子の保存

## 概要
対角のHom比較と中間制限比較による右単位子の保存。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section RightUnitRestriction
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D C)

/-- 対角比較をtensorし、中間比較とYoneda評価を続けると制限後の右単位になる。 -/
lemma rightUnitRestriction_value (P : BimoduleCategory A B C) (b : B) (d : D) :
    composeValueMap A B D D
        (𝟙 ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P))
        (Bimodule.diagonalRestrictionMap A D C F) b d ≫
      middleRestrictionComparisonValue A B C D D F (BimoduleCategory.underlying A B C P)
        (Bimodule.leftRestriction A C C D F (Bimodule.diagonal A C)) b d ≫
      (rightUnitValueIso A B C (BimoduleCategory.underlying A B C P) b (F.obj d)).hom =
    (rightUnitValueIso A B D
      (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)) b d).hom := by
  apply BalancedTensor.hom_ext
  intro x
  erw [ι_composeValueMap_assoc A B D D
    (𝟙 ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P))
    (Bimodule.diagonalRestrictionMap A D C F) b x d, Bimodule.diagonalRestrictionMap_value,
    CategoryTheory.Functor.map_id]
  erw [ι_middleRestrictionComparisonValue_assoc A B C D D F
    (BimoduleCategory.underlying A B C P)
    (Bimodule.leftRestriction A C C D F (Bimodule.diagonal A C)) b d x]
  change (F.map x d ⊗ₘ 𝟙 _) ≫ BalancedTensor.ι A C
      (representable A (F.obj d)) ((BimoduleCategory.underlying A B C P).leftAt b)
      (F.obj x) ≫ BalancedTensor.yonedaEvaluation A C (F.obj d)
        ((BimoduleCategory.underlying A B C P).leftAt b) =
    BalancedTensor.ι A D (representable A d)
      ((Bimodule.leftRestriction A B C D F
        (BimoduleCategory.underlying A B C P)).leftAt b) x ≫
      BalancedTensor.yonedaEvaluation A D d
        ((Bimodule.leftRestriction A B C D F
          (BimoduleCategory.underlying A B C P)).leftAt b)
  rw [BalancedTensor.ι_yonedaEvaluation, BalancedTensor.ι_yonedaEvaluation]
  have hl : BalancedTensor.leftAction A D
      ((Bimodule.leftRestriction A B C D F
        (BimoduleCategory.underlying A B C P)).leftAt b) x d =
    BalancedTensor.leftAction A D (F.comp ((BimoduleCategory.underlying A B C P).leftAt b))
      x d := by
    change uncurryRight ((F.map x d ≫ (BimoduleCategory.underlying A B C P).map
      (F.obj x) (F.obj d)) ≫ moduleHomπ A B _ _ b) =
      uncurryRight (F.map x d ≫ ((BimoduleCategory.underlying A B C P).map
        (F.obj x) (F.obj d) ≫ moduleHomπ A B _ _ b))
    rw [Category.assoc]
  rw [hl]
  exact (BalancedTensor.leftAction_restrict A D C F
    ((BimoduleCategory.underlying A B C P).leftAt b) x d).symm

/-- 右単位子は対角のHom比較・中間比較・外側左制限比較と整合する。 -/
lemma rightUnitRestriction (P : BimoduleCategory A B C) :
    composeMap A B D D
        (𝟙 ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P))
        (Bimodule.diagonalRestrictionMap A D C F) ≫
      middleRestrictionComparisonMap A B C D D F (BimoduleCategory.underlying A B C P)
        (Bimodule.leftRestriction A C C D F (Bimodule.diagonal A C)) ≫
      (composeLeftRestrictionIso A B C C D F P
        (BimoduleCategory.of A C C (Bimodule.diagonal A C))).hom ≫
      (BimoduleCategory.middleLeftRestrictionFunctor A B C D F).map
        (rightBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom =
    (rightBimoduleUnitIso A B D
      (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P))).hom := by
  apply BimoduleCategory.value_hom_ext A B D
  intro b d
  simp only [CategoryTheory.Functor.map_comp, composeMap_value_eval,
    middleRestrictionComparisonMap_value_eval, composeLeftRestrictionIso_hom_value]
  erw [BimoduleCategory.middleLeftRestrictionMap_value_eval]
  rw [rightBimoduleUnitIso_hom_value, rightBimoduleUnitIso_hom_value]
  erw [Category.id_comp]
  exact rightUnitRestriction_value A B C D F P b d

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end RightUnitRestriction

/-! ## FunctorExtensionProjection（旧 SerrePositivity/DifferentialGraded/Tensor/FunctorExtensionProjection.lean） -/

/-! # graph延長とtensorの射影公式：Fubiniと全Hom自然なYoneda評価

## 概要
graph延長とtensorの射影公式：Fubiniと全Hom自然なYoneda評価。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section FunctorExtensionProjection
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

omit [Small.{u} D] in
lemma graphTensorYoneda_naturality (N : LeftModule A E) (x y : D) :
    (Fubini.leftModule A E D (functorGraph A D E F) N).map x y ≫
      homPostcompose _ (yonedaIso A E (F.obj y) N).hom =
    (F.comp N).map x y ≫ homPrecompose (yonedaIso A E (F.obj x) N).hom _ := by
  change ((F.map x y ≫ yonedaHom A E (F.obj x) (F.obj y)) ≫
    rightHomMap A E (representable A (F.obj x)) (representable A (F.obj y)) N) ≫
      homPostcompose (obj A E (representable A (F.obj x)) N)
        (yonedaEvaluation A E (F.obj y) N) =
      (F.map x y ≫ N.map (F.obj x) (F.obj y)) ≫
        homPrecompose (yonedaEvaluation A E (F.obj x) N) (N.obj (F.obj y))
  simpa only [Category.assoc] using
    congrArg (fun k => F.map x y ≫ k)
      (yonedaEvaluation_representative_naturality A E N (F.obj x) (F.obj y))

/-- graphとのtensorのYoneda評価は全次数自然な左D加群同型。 -/
def graphTensorYonedaIso (N : LeftModule A E) :
    ForgetEnrichment.of (Complex A) (Fubini.leftModule A E D (functorGraph A D E F) N) ≅
      ForgetEnrichment.of (Complex A) (F.comp N) :=
  (leftModuleToRightOppositeFullyFaithful A D).preimageIso
    (X := ForgetEnrichment.of (Complex A)
      (Fubini.leftModule A E D (functorGraph A D E F) N))
    (Y := ForgetEnrichment.of (Complex A) (F.comp N))
    (moduleIsoMk A Dᵒᵖ
      (M := (Fubini.leftModule A E D (functorGraph A D E F) N).toRightOpposite)
      (N := LeftModule.toRightOpposite (F.comp N))
      (fun x => yonedaIso A E (F.obj x.unop.unop) N)
      (leftFamily_rightOpposite_naturality A D
        (M := Fubini.leftModule A E D (functorGraph A D E F) N) (N := F.comp N)
        (fun x => (yonedaIso A E (F.obj x) N).hom)
        (graphTensorYoneda_naturality A D E F N)))

@[simp]
lemma graphTensorYonedaIso_hom_eval (N : LeftModule A E) (d : D) :
    (leftModuleEvaluation A D d).map (graphTensorYonedaIso A D E F N).hom =
      (yonedaIso A E (F.obj d) N).hom :=
  moduleIsoMk_hom_eval A Dᵒᵖ
    (M := (Fubini.leftModule A E D (functorGraph A D E F) N).toRightOpposite)
    (N := LeftModule.toRightOpposite (F.comp N))
    (fun x => yonedaIso A E (F.obj x.unop.unop) N)
    (leftFamily_rightOpposite_naturality A D
      (M := Fubini.leftModule A E D (functorGraph A D E F) N) (N := F.comp N)
      (fun x => (yonedaIso A E (F.obj x) N).hom)
      (graphTensorYoneda_naturality A D E F N)) (op d)

/-- 任意の右D加群と左E加群について、延長とtensorを交換する実際の複体同型。 -/
def functorExtensionTensorIso (R : RightModule A D) (N : LeftModule A E) :
    obj A E ((dgModuleExtension A D E F).obj R) N ≅ obj A D R (F.comp N) :=
  (Fubini.iso A E D (functorGraph A D E F) R N).symm ≪≫
    (leftTensorFunctor A D R).mapIso (graphTensorYonedaIso A D E F N)

/-- 射影公式はR,graph,Nの順の三重生成元をYonedaの左作用で評価する。 -/
@[reassoc]
lemma rightι_functorExtensionTensorIso_hom (R : RightModule A D) (N : LeftModule A E)
    (e : E) (d : D) :
    Fubini.rightι A E D (functorGraph A D E F) R N e d ≫
        (functorExtensionTensorIso A D E F R N).hom =
      (R.obj (op d) ◁ leftAction A E N e (F.obj d)) ≫ ι A D R (F.comp N) d := by
  change Fubini.rightι A E D (functorGraph A D E F) R N e d ≫
    (Fubini.iso A E D (functorGraph A D E F) R N).inv ≫
      (leftTensorFunctor A D R).map (graphTensorYonedaIso A D E F N).hom = _
  rw [Fubini.rightι_iso_inv_assoc]
  change (R.obj (op d) ◁ ι A E (representable A (F.obj d)) N e) ≫
    ι A D R (Fubini.leftModule A E D (functorGraph A D E F) N) d ≫
      map A D (𝟙 (ForgetEnrichment.of (Complex A) R))
        (graphTensorYonedaIso A D E F N).hom = _
  have hm := ι_map A D (𝟙 (ForgetEnrichment.of (Complex A) R))
    (graphTensorYonedaIso A D E F N).hom d
  simp only [CategoryTheory.Functor.map_id, graphTensorYonedaIso_hom_eval, id_tensorHom] at hm
  refine (congrArg (fun k =>
    (R.obj (op d) ◁ ι A E (representable A (F.obj d)) N e) ≫ k) hm).trans ?_
  change (R.obj (op d) ◁ ι A E (representable A (F.obj d)) N e) ≫
    (R.obj (op d) ◁ yonedaEvaluation A E (F.obj d) N) ≫ ι A D R (F.comp N) d = _
  rw [← whiskerLeft_comp_assoc, ι_yonedaEvaluation]

/-- graph延長は右相対K-flat性を保つ。Homや左因子のflatnessは不要。 -/
lemma functorExtension_relativeKFlat (R : RightModule A D)
    (hR : moduleRelativeKFlat A D R) :
    moduleRelativeKFlat A E ((dgModuleExtension A D E F).obj R) := by
  intro N hN
  have hr := hR (F.comp N) (fun d => hN (F.obj d))
  exact cochainAcyclic_of_iso hr (functorExtensionTensorIso A D E F R N).symm

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end FunctorExtensionProjection
