module
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleMiddleActions
public import SerrePositivity.DifferentialGraded.Bimodule.Category
public import SerrePositivity.DifferentialGraded.Bimodule.ValueExt
public import SerrePositivity.DifferentialGraded.Module.HomSquareComposition

/-! # 中間dg圏の制限と合成の全Hom自然なbimodule比較射

## 概要
中間dg圏の制限と合成の全Hom自然なbimodule比較射。

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
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)
  (P : Bimodule A B C) (Q : Bimodule A C E)

/-- 各左対象で、値のchain mapを全Hom自然な右加群射へ束ねる。 -/
def middleRestrictionComparisonRightMap (e : E) :
    ForgetEnrichment.of (Complex A)
      ((compose A B D E (Bimodule.leftRestriction A B C D F P)
        (Bimodule.rightRestriction A C D E F Q)).rightAt e) ⟶
      ForgetEnrichment.of (Complex A) ((compose A B C E P Q).rightAt e) :=
  moduleMorphismMk A B
    (fun b => middleRestrictionComparisonValue A B C D E F P Q b.unop e)
    (fun b b' => middleRestrictionComparisonValue_right_naturality A B C D E F P Q b b' e)

@[simp]
lemma middleRestrictionComparisonRightMap_eval (b : B) (e : E) :
    (moduleEvaluation A B b).map (middleRestrictionComparisonRightMap A B C D E F P Q e) =
      middleRestrictionComparisonValue A B C D E F P Q b e :=
  moduleMorphismMk_eval A B _ _ b

@[simp]
lemma middleRestrictionComparisonRightMap_component (b : B) (e : E) :
    moduleMorphismComponent A B
      ((compose A B D E (Bimodule.leftRestriction A B C D F P)
        (Bimodule.rightRestriction A C D E F Q)).rightAt e)
      ((compose A B C E P Q).rightAt e)
      (middleRestrictionComparisonRightMap A B C D E F P Q e) b =
        middleRestrictionComparisonValue A B C D E F P Q b e :=
  middleRestrictionComparisonRightMap_eval A B C D E F P Q b e

lemma middleRestrictionComparisonRightMap_naturality (e e' : E) :
    (compose A B D E (Bimodule.leftRestriction A B C D F P)
        (Bimodule.rightRestriction A C D E F Q)).map e e' ≫
      moduleHomPostcompose A B _ _ _ (middleRestrictionComparisonRightMap A B C D E F P Q e') =
    (compose A B C E P Q).map e e' ≫
      moduleHomPrecompose A B _ _ _ (middleRestrictionComparisonRightMap A B C D E F P Q e) := by
  apply moduleHom_ext
  intro b
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  simp only [middleRestrictionComparisonRightMap_component]
  have h := middleRestrictionComparisonValue_left_naturality A B C D E F P Q b e e'
  change (((compose A B D E (Bimodule.leftRestriction A B C D F P)
      (Bimodule.rightRestriction A C D E F Q)).map e e') ≫ moduleHomπ A B _ _ b) ≫ _ =
    ((compose A B C E P Q).map e e' ≫ moduleHomπ A B _ _ b) ≫ _ at h
  exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))

/-- 中間圏を制限してから合成するbimoduleから、元の合成への実際の閉零射。 -/
def middleRestrictionComparisonMap :
    BimoduleCategory.of A B E (compose A B D E (Bimodule.leftRestriction A B C D F P)
      (Bimodule.rightRestriction A C D E F Q)) ⟶
        BimoduleCategory.of A B E (compose A B C E P Q) :=
  ⟨middleRestrictionComparisonRightMap A B C D E F P Q,
    middleRestrictionComparisonRightMap_naturality A B C D E F P Q⟩

@[simp]
lemma middleRestrictionComparisonMap_value_eval (b : B) (e : E) :
    (BimoduleCategory.valueEvaluation A B E b e).map
        (middleRestrictionComparisonMap A B C D E F P Q) =
      middleRestrictionComparisonValue A B C D E F P Q b e :=
  middleRestrictionComparisonRightMap_eval A B C D E F P Q b e

end SerrePositivity.DifferentialGraded.BimoduleTensor
