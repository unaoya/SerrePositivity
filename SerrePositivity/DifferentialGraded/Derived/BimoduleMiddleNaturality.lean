module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleComparison
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions

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
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
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
