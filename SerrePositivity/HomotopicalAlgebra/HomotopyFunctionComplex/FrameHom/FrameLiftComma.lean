module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLiftSimplices
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Equivalence

/-!
# 分解の comma 圏と全持ち上げ単体の反対要素圏

概要：Low 命題 3.6 の分解の comma 圏を元の持ち上げ空間で表示する。
方針：元の fiber の全単体と可換三角形の全単射を全作用素へ拡張する。
規約：comma 圏の射は元の単体作用素と三角形の整合を保持する。
使われ方：分解から自明 fibration への comma 圏の可縮性の証明。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C]
  (A : SimplexCategory ⥤ C) {X E B : C}
  (a : A ⟶ (Functor.const SimplexCategory).obj X) (p : E ⟶ B) (f : X ⟶ B)

/-- 概要：分解の augmentation は元の slice 圏への関手（Low 命題 3.6）。
方針：元の augmentation の自然性を全三角形の整合に使う。
規約：指定した係数射の後の元の augmentation を保持する。
使われ方：持ち上げを表す comma 圏の元の関手。 -/
def overFunctor : SimplexCategory ⥤ Over B where
  obj n := Over.mk (a.app n ≫ f)
  map {n m} θ := Over.homMk (A.map θ) (by
    have h := a.naturality θ
    change A.map θ ≫ a.app _ = a.app _ ≫ 𝟙 X at h
    exact (Category.assoc (A.map θ) (a.app m) f).symm.trans
      (congrArg (fun k => k ≫ f) (h.trans (Category.comp_id _))))
  map_id n := Over.OverMorphism.ext (A.map_id n)
  map_comp θ φ := Over.OverMorphism.ext (A.map_comp θ φ)

/-- 概要：全持ち上げ単体を元の comma 圏へ送る（Low 命題 3.6）。
方針：元の fiber の包含と全単体作用素の自然性を使う。
規約：元の持ち上げ射を comma 対象の射に使う。
使われ方：comma 圏の可縮性の全単体表示。 -/
def toComma : (LiftSpace.obj A a p f).Elementsᵒᵖ ⥤
    CostructuredArrow (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.overFunctor A a f) (Over.mk p) where
  obj s := CostructuredArrow.mk (Y := s.unop.obj.unop) (Over.homMk
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.simplexEquiv A a p f s.unop.obj s.unop.val).val
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.simplexEquiv A a p f s.unop.obj s.unop.val).property)
  map {s t} θ := CostructuredArrow.homMk θ.unop.hom.unop (by
    apply Over.OverMorphism.ext
    change A.map θ.unop.hom.unop ≫
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.simplexEquiv A a p f t.unop.obj t.unop.val).val =
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.simplexEquiv A a p f s.unop.obj s.unop.val).val
    rw [← _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.simplexEquiv_naturality, θ.unop.map_val])
  map_id s := CostructuredArrow.hom_ext _ _ rfl
  map_comp θ φ := CostructuredArrow.hom_ext _ _ rfl

/-- 概要：comma 比較は元の全単体作用素を区別する（Low 命題 3.6）。
方針：元の単体作用素は comma の射の左成分として回収される。
規約：射をホモトピー類へ落とさない。
使われ方：持ち上げ単体表示の圏同値。 -/
instance toComma_faithful : (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.toComma A a p f).Faithful where
  map_injective {s t} θ φ h := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    exact congrArg (fun k => k.left.op) h

/-- 概要：全ての可換単体作用素は元の要素圏の射から来る（Low 命題 3.6）。
方針：元の包含の単射性と comma の三角形の可換性を使う。
規約：元の作用素をそのまま逆像に使う。
使われ方：持ち上げ単体表示の充満性。 -/
instance toComma_full : (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.toComma A a p f).Full where
  map_surjective {s t} θ := by
    let k : s ⟶ t := Quiver.Hom.op (Functor.Elements.homMk θ.left.op (by
      apply _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.inclusion_injective A a p f s.unop.obj
      change (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.simplexEquiv A a p f s.unop.obj
          ((LiftSpace.obj A a p f).map θ.left.op t.unop.val)).val =
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.simplexEquiv A a p f s.unop.obj s.unop.val).val
      exact (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.simplexEquiv_naturality A a p f θ.left.op t.unop.val).trans
        (congrArg (fun g => g.left) (CostructuredArrow.w θ))))
    exact ⟨k, CostructuredArrow.hom_ext _ _ rfl⟩

/-- 概要：comma の全持ち上げ対象は同じ fiber の単体から来る（Low 命題 3.6）。
方針：全単体の全単射の逆を同じ可換三角形へ適用する。
規約：次元と元の持ち上げ射を保持する。
使われ方：持ち上げ単体表示の本質的全射性。 -/
instance toComma_essSurj : (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.toComma A a p f).EssSurj where
  mem_essImage c := by
    let g : {g : A.obj c.left ⟶ E // g ≫ p = a.app c.left ≫ f} :=
      ⟨c.hom.left, Over.w c.hom⟩
    let s := op ((LiftSpace.obj A a p f).elementsMk (op c.left)
      ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.simplexEquiv A a p f (op c.left)).symm g))
    refine ⟨s, ⟨CostructuredArrow.isoMk (Iso.refl c.left) ?_⟩⟩
    apply Over.OverMorphism.ext
    change A.map (𝟙 c.left) ≫ c.hom.left =
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.simplexEquiv A a p f (op c.left) ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.simplexEquiv A a p f (op c.left)).symm g)).val
    rw [A.map_id, Category.id_comp]
    exact (congrArg Subtype.val ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.simplexEquiv A a p f (op c.left)).apply_symm_apply g)).symm

/-- 概要：分解の comma 圏は全持ち上げ単体の反対要素圏と同値（Low 命題 3.6）。
方針：元の全単体表示の充満忠実性と本質的全射性を束ねる。
規約：同値の順関手は元の包含と同じ toComma。
使われ方：comma の nerve の全次数の可縮性。 -/
def commaEquivalence : (LiftSpace.obj A a p f).Elementsᵒᵖ ≌
    CostructuredArrow (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.overFunctor A a f) (Over.mk p) := by
  let : (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.toComma A a p f).IsEquivalence := {}
  exact (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.toComma A a p f).asEquivalence

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift
