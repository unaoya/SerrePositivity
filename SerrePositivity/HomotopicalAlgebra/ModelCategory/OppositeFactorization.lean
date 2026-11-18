module

public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# 関手的分解の反対圏への移送

概要：Hovey §1.1 の関手的分解を左右を交換して反対圏へ移す。
方針：可換正方形を反転し、中間対象と二つの自然変換を反対化する。
規約：モデル構造の存在は不要、指定した射の二つのクラスを使う。
使われ方：E 代数の右 frame と重み付き homotopy 極限の構成。
-/

@[expose] public section

universe v u

namespace SerrePositivity.OppositeFactorization.OppositeFactorization

open _root_.CategoryTheory _root_.Opposite

variable {C : Type u} [Category.{v} C]

/-- 概要：反対圏の射と正方形を元の反対射圏へ移す（Hovey §1.1）。
方針：正方形の左右の射を入れ替えて unop する。
規約：元の可換正方形を保持する。
使われ方：中間対象の関手性を反対圏で構成する。 -/
def arrowUnop : Arrow Cᵒᵖ ⥤ (Arrow C)ᵒᵖ where
  obj f := op (Arrow.mk f.hom.unop)
  map φ := (Arrow.homMk φ.right.unop φ.left.unop
    (congrArg Quiver.Hom.unop (Arrow.w φ)).symm).op
  map_id _ := by
    apply Quiver.Hom.unop_inj
    ext <;> rfl
  map_comp _ _ := by
    apply Quiver.Hom.unop_inj
    ext <;> rfl

/-- 概要：関手的な二段分解を反対圏へ移す（Hovey §1.1）。
方針：中間対象の関手と二つの自然変換を反転し、左右の類を交換する。
規約：分解の選択は元のデータと同じで、新しい選択を行わない。
使われ方：E 代数の反対圏で関手的 cofibrant 分解を得る。 -/
def opposite {W₁ W₂ : MorphismProperty C}
    (d : MorphismProperty.FunctorialFactorizationData W₁ W₂) :
    MorphismProperty.FunctorialFactorizationData W₂.op W₁.op where
  Z := _root_.SerrePositivity.OppositeFactorization.OppositeFactorization.arrowUnop ⋙ d.Z.op
  i :=
    { app f := (d.p.app (Arrow.mk f.hom.unop)).op
      naturality {_ _} φ := by
        exact (congrArg Quiver.Hom.op (d.p.naturality (_root_.SerrePositivity.OppositeFactorization.OppositeFactorization.arrowUnop.map φ).unop)).symm }
  p :=
    { app f := (d.i.app (Arrow.mk f.hom.unop)).op
      naturality {_ _} φ := by
        exact (congrArg Quiver.Hom.op (d.i.naturality (_root_.SerrePositivity.OppositeFactorization.OppositeFactorization.arrowUnop.map φ).unop)).symm }
  fac := by
    ext f
    exact d.fac_app (f := Arrow.mk f.hom.unop)
  hi f := d.hp (Arrow.mk f.hom.unop)
  hp f := d.hi (Arrow.mk f.hom.unop)

end SerrePositivity.OppositeFactorization.OppositeFactorization
