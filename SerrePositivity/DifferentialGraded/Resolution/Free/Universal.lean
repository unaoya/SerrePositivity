module
public import SerrePositivity.DifferentialGraded.Resolution.Free.Reconstruction

/-! # 自由dg圏の対象写像・生成辺に関する厳密普遍性

## 概要
自由dg圏の対象写像・生成辺に関する厳密普遍性。

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
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) [DGCategory A E]

/-- 自由dg圏への入力。対象写像と各生成辺のchain mapだけを指定する。 -/
structure GeneratorMap (K : ComplexQuiver A D) where
  obj : D → E
  map : ∀ x y, K x y ⟶ (obj x ⟶[Complex A] obj y)

variable [Small.{u} D]

def restrict (K : ComplexQuiver A D) (F : DGFunctor A (Objects A D K) E) :
    GeneratorMap A D E K where
  obj := F.obj
  map x y := edgeInclusion A D K x y ≫ F.map x y

def extend (K : ComplexQuiver A D) (g : GeneratorMap A D E K) : DGFunctor A (Objects A D K) E :=
  lift A D E K g.obj g.map

lemma extend_restrict (K : ComplexQuiver A D) (F : DGFunctor A (Objects A D K) E) :
    extend A D E K (restrict A D E K F) = F := lift_reconstruction A D E K F

lemma restrict_extend (K : ComplexQuiver A D) (g : GeneratorMap A D E K) :
    restrict A D E K (extend A D E K g) = g := by
  cases g with
  | mk o f =>
    change (⟨o, fun x y => edgeInclusion A D K x y ≫ (lift A D E K o f).map x y⟩ :
      GeneratorMap A D E K) = ⟨o, f⟩
    congr 1
    funext x y
    exact lift_edge A D E K o f x y

/-- 自由dg圏上のdg関手と対象・辺の入力データの型の厳密な同値。 -/
def universalEquiv (K : ComplexQuiver A D) :
    DGFunctor A (Objects A D K) E ≃ GeneratorMap A D E K where
  toFun := restrict A D E K
  invFun := extend A D E K
  left_inv := extend_restrict A D E K
  right_inv := restrict_extend A D E K

lemma extension_unique (K : ComplexQuiver A D) (g : GeneratorMap A D E K)
    (F : DGFunctor A (Objects A D K) E) (h : restrict A D E K F = g) :
    F = extend A D E K g := by
  rw [← h, extend_restrict]

end SerrePositivity.DifferentialGraded.FreeDGCategory
