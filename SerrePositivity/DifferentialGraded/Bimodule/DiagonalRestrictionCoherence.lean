module
public import SerrePositivity.DifferentialGraded.Bimodule.DiagonalRestriction
public import SerrePositivity.DifferentialGraded.Bimodule.PairedRestrictionCoherence

/-! # Hom写像による対角制限比較の恒等・合成則

## 概要
Hom写像による対角制限比較の恒等・合成則。

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
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 恒等関手の対角比較は既存の恒等制限比較の逆射。 -/
lemma diagonalRestrictionMap_id :
    diagonalRestrictionMap A D D (DGFunctor.id D) ≫
        (BimoduleCategory.pairedRestrictionIdObjIso A D D
          (BimoduleCategory.of A D D (diagonal A D))).hom = 𝟙 _ := by
  apply BimoduleCategory.value_hom_ext A D D
  intro b d
  rw [CategoryTheory.Functor.map_comp, diagonalRestrictionMap_value,
    BimoduleCategory.pairedRestrictionIdObjIso_hom_value, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : Type z) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 二段階のHom写像による対角比較は、合成dg関手の比較そのもの。 -/
lemma diagonalRestrictionMap_comp :
    diagonalRestrictionMap A D E F ≫
        (BimoduleCategory.pairedRestrictionFunctor A E E D D F F).map
          (diagonalRestrictionMap A E T G) ≫
        (BimoduleCategory.pairedRestrictionCompObjIso A T T E E D D F G F G
          (BimoduleCategory.of A T T (diagonal A T))).hom =
      diagonalRestrictionMap A D T (F.comp G) := by
  apply BimoduleCategory.value_hom_ext A D D
  intro b d
  simp only [CategoryTheory.Functor.map_comp, diagonalRestrictionMap_value,
    BimoduleCategory.pairedRestrictionFunctor_map_value,
    BimoduleCategory.pairedRestrictionCompObjIso_hom_value, Category.comp_id]
  rfl

end SerrePositivity.DifferentialGraded.Bimodule
