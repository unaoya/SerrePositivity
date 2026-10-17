module
public import SerrePositivity.DifferentialGraded.Tensor.LeftUnitRestriction
public import SerrePositivity.DifferentialGraded.Tensor.ComposeRightRestrictionNaturality
public import SerrePositivity.DifferentialGraded.Tensor.UnitMapNaturality

/-! # 制限後の指定増大射による左単位squareの計算

## 概要
制限後の指定増大射による左単位squareの計算。

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
universe u v w z
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
