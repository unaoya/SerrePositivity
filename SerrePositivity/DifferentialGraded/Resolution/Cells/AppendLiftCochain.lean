module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.CompositionPrefix
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathEquations
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryRowRecursion
public import SerrePositivity.DifferentialGraded.Complexes.PrefixTensorCochainAction

/-! # 任意次数cell pathの境界置換：AppendLiftCochain

## 概要
任意次数cell pathの境界置換：AppendLiftCochain。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

/-- 前方Homと生成元を付け直し、後方の連結cochainを全pathへ戻す。 -/
def appendLiftCochain (b : I) (w : List I) (x y z : D) (p : ℤ)
    (f : Cochain (C.term A D I w (C.target b) y ⊗ C.internalHom A D I y z)
      (C.internalHom A D I (C.target b) z) p) :
    Cochain (C.term A D I (b :: w) x y ⊗ C.internalHom A D I y z) (C.internalHom A D I x z) p :=
  ((Cochain.ofHom ((α_ (homObject A D x (C.source b))
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
      (homObject A D x (C.source b)) ◁
        (α_ (C.generator A D I b) (C.term A D I w (C.target b) y) (C.internalHom A D I y
          z)).hom)).comp
    ((tensorLeftHom (homObject A D x (C.source b))
      (C.generator A D I b ⊗ (C.term A D I w (C.target b) y ⊗ C.internalHom A D I y z))
      (C.generator A D I b ⊗ C.internalHom A D I (C.target b) z)).f p
      ((tensorLeftHom (C.generator A D I b) (C.term A D I w (C.target b) y ⊗ C.internalHom A D I y
        z)
        (C.internalHom A D I (C.target b) z)).f p f)) (zero_add p)).comp
      (Cochain.ofHom (C.prefixPath A D I b x z)) (add_zero p)

lemma appendLiftCochain_add (b : I) (w : List I) (x y z : D) (p : ℤ)
    (f g : Cochain (C.term A D I w (C.target b) y ⊗ C.internalHom A D I y z)
      (C.internalHom A D I (C.target b) z) p) :
    C.appendLiftCochain A D I b w x y z p (f + g) =
      C.appendLiftCochain A D I b w x y z p f + C.appendLiftCochain A D I b w x y z p g := by
  simp only [appendLiftCochain, map_add]
  rw [Cochain.comp_add _ _ _ (zero_add p)]
  exact Cochain.add_comp _ _ _ (add_zero p)

/-- 左語の後方cochainによる項は、短い語での項の持ち上げに等しい。 -/
lemma appendLiftCochain_left (b : I) (w : List I) (x y z : D) (p : ℤ)
    (f : Cochain (C.term A D I w (C.target b) y) (C.internalHom A D I (C.target b) y) p) :
    ((tensorRightHom (C.internalHom A D I y z) (C.term A D I (b :: w) x y)
      (C.internalHom A D I x y)).f p (C.prefixTailCochain A D I b w x y p f)).comp
      (Cochain.ofHom (C.internalComposition A D I x y z)) (add_zero p) =
    C.appendLiftCochain A D I b w x y z p
      (((tensorRightHom (C.internalHom A D I y z) (C.term A D I w (C.target b) y)
        (C.internalHom A D I (C.target b) y)).f p f).comp
          (Cochain.ofHom (C.internalComposition A D I (C.target b) y z)) (add_zero p)) := by
  have ha := C.internalComposition_prefixPath A D I b x y z
  simp only [whiskerLeft_comp, Category.assoc] at ha
  have h := prefixTensor_cochain_action_left (homObject A D x (C.source b))
    (C.generator A D I b) (C.term A D I w (C.target b) y)
    (C.internalHom A D I (C.target b) y) (C.internalHom A D I y z)
    (C.internalHom A D I x y) (C.internalHom A D I (C.target b) z)
    (C.internalHom A D I x z) p f (C.prefixPath A D I b x y)
    (C.internalComposition A D I x y z) (C.internalComposition A D I (C.target b) y z)
    (C.prefixPath A D I b x z) ha
  unfold prefixTailCochain appendLiftCochain
  simp only [term_cons]
  change ((tensorRightHom (C.internalHom A D I y z)
      (homObject A D x (C.source b) ⊗
        (C.generator A D I b ⊗ C.term A D I w (C.target b) y))
      (C.internalHom A D I x y)).f p
      (((tensorLeftHom (homObject A D x (C.source b)) _ _).f p
        ((tensorLeftHom (C.generator A D I b) _ _).f p f)).comp
        (Cochain.ofHom (C.prefixPath A D I b x y)) (add_zero p))).comp
      (Cochain.ofHom (C.internalComposition A D I x y z)) (add_zero p) = _
  with_reducible exact h

/-- 右側cochainによる項も短い語での項の持ち上げに等しい。 -/
lemma appendLiftCochain_right (b : I) (w : List I) (x y z : D) (p : ℤ)
    (f : Cochain (C.internalHom A D I y z) (C.internalHom A D I y z) p) :
    ((tensorLeftHom (C.term A D I (b :: w) x y) (C.internalHom A D I y z)
      (C.internalHom A D I y z)).f p f).comp
      (Cochain.ofHom (C.appendRight A D I (b :: w) x y z)) (add_zero p) =
    C.appendLiftCochain A D I b w x y z p
      (((tensorLeftHom (C.term A D I w (C.target b) y) (C.internalHom A D I y z)
        (C.internalHom A D I y z)).f p f).comp
          (Cochain.ofHom (C.appendRight A D I w (C.target b) y z)) (add_zero p)) := by
  let cmp : (homObject A D x (C.source b) ⊗
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y)) ⊗ C.internalHom A D I y z ⟶
      C.internalHom A D I x z := C.appendRight A D I (b :: w) x y z
  have ha := C.appendRight_cons A D I b w x y z
  simp only [whiskerLeft_comp, Category.assoc] at ha
  have h := prefixTensor_cochain_action_right (homObject A D x (C.source b))
    (C.generator A D I b) (C.term A D I w (C.target b) y)
    (C.internalHom A D I y z) (C.internalHom A D I y z)
    (C.internalHom A D I (C.target b) z) (C.internalHom A D I x z) p f
    cmp (C.appendRight A D I w (C.target b) y z) (C.prefixPath A D I b x z) ha
  unfold appendLiftCochain
  simp only [term_cons]
  change ((tensorLeftHom (homObject A D x (C.source b) ⊗
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y))
      (C.internalHom A D I y z) (C.internalHom A D I y z)).f p f).comp
      (Cochain.ofHom cmp) (add_zero p) = _
  with_reducible exact h

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
