module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.IndexOppositeEquivalence
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Objects
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# latching側の余極限を反変Homでmatching側の極限へ移す同型を構成する

## 概要
latching側の余極限を反変Homでmatching側の極限へ移す同型を構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
Reedy境界の添字と比較写像を明示し、境界の普遍性を照合する。
次数ごとの構成を既存の低次数の系と整合させる。

## 規約と注意
圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
表示された圏や比較射を、局所化後の同型だけで置き換えない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0262][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0262
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Contravariant boundary Hom sends latching colimits to matching limits

The result is for any contravariant functor preserving the particular
opposite latching limit. Its comparison formula identifies the actual
matching map, rather than only its source and target objects.
-/

@[expose] public section
universe v u t vV uV vW uW
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite

namespace SerrePositivity.Reedy.BoundaryHom
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J)
  {V : Type uV} [Category.{vV} V] {W : Type uW} [Category.{vW} W]
  (A : J ⥤ V) (H : Vᵒᵖ ⥤ W)
  [HasColimitsOfShape (LatchingIndex r j) V]

/-- The canonical cone obtained from the opposite of the actual latching cocone. -/
abbrev cone : Cone (matchingTarget r.op (op j) ⋙ A.op ⋙ H) :=
  (H.mapCone (colimit.cocone (latchingSource r j ⋙ A)).op).whisker (matchingOpFunctor r j)

variable [PreservesLimit (latchingSource r j ⋙ A).op H]

/-- The limit property follows from duality, preservation, and the actual index equivalence. -/
def isLimit : IsLimit (cone r j A H) :=
  (isLimitOfPreserves H (colimit.isColimit (latchingSource r j ⋙ A)).op).whiskerEquivalence
    (matchingOpEquivalence r j)

variable [HasLimitsOfShape (MatchingIndex r.op (op j)) W]

/- 旧宣言の技術注記：The concrete boundary-Hom object is the actual matching object. -/
/-- latching側の余極限を反変Homでmatching側の極限へ移す同型を構成する。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
Reedy境界の添字と比較写像を明示し、境界の普遍性を照合する。
次数ごとの構成を既存の低次数の系と整合させる。
-/

def iso : H.obj (op ((latchingEvaluation r j).obj A)) ≅
    (matchingEvaluation r.op (op j)).obj (A.op ⋙ H) :=
  (isLimit r j A H).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)]
lemma iso_hom_π (f : MatchingIndex r.op (op j)) :
    (iso r j A H).hom ≫ limit.π (matchingTarget r.op (op j) ⋙ A.op ⋙ H) f =
      H.map (colimit.ι (latchingSource r j ⋙ A) (matchingOpObjEquiv r j f)).op :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ f

/-- The actual matching comparison is contravariant application of the latching comparison. -/
@[reassoc]
lemma comparison :
    H.map ((latchingComparison r j).app A).op ≫ (iso r j A H).hom =
      (matchingComparison r.op (op j)).app (A.op ⋙ H) := by
  apply limit.hom_ext
  intro f
  rw [Category.assoc]
  refine (congrArg (fun k => H.map ((latchingComparison r j).app A).op ≫ k)
    (iso_hom_π r j A H f)).trans ?_
  refine Eq.trans ?_ (limit.lift_π (matchingCone r.op (A.op ⋙ H) (op j)) f).symm
  change H.map ((latchingComparison r j).app A).op ≫
      H.map (colimit.ι (latchingSource r j ⋙ A) (matchingOpObjEquiv r j f)).op =
    H.map (A.map f.obj.hom.unop).op
  rw [← H.map_comp, ← op_comp]
  exact congrArg H.map (congrArg Quiver.Hom.op
    (colimit.ι_desc (latchingCocone r A j) (matchingOpObjEquiv r j f)))

/-- The boundary comparison is natural in a transformation of contravariant functors. -/
@[reassoc]
lemma iso_naturality {H' : Vᵒᵖ ⥤ W}
    [PreservesLimit (latchingSource r j ⋙ A).op H'] (τ : H ⟶ H') :
    (iso r j A H).hom ≫ (matchingEvaluation r.op (op j)).map (Functor.whiskerLeft A.op τ) =
      τ.app (op ((latchingEvaluation r j).obj A)) ≫ (iso r j A H').hom := by
  apply limit.hom_ext
  intro f
  let t := Functor.whiskerLeft (matchingTarget r.op (op j)) (Functor.whiskerLeft A.op τ)
  change ((iso r j A H).hom ≫ lim.map t) ≫
      limit.π (matchingTarget r.op (op j) ⋙ A.op ⋙ H') f = _
  rw [Category.assoc, limit.map_π]
  change (iso r j A H).hom ≫
      (limit.π (matchingTarget r.op (op j) ⋙ A.op ⋙ H) f ≫
        τ.app (op (A.obj f.obj.right.unop))) = _
  rw [← Category.assoc]
  refine (congrArg (fun k => k ≫ τ.app (op (A.obj f.obj.right.unop)))
    (iso_hom_π r j A H f)).trans ?_
  have he := τ.naturality
    (colimit.ι (latchingSource r j ⋙ A) (matchingOpObjEquiv r j f)).op
  exact he.trans ((congrArg (fun k => τ.app (op ((latchingEvaluation r j).obj A)) ≫ k)
    (iso_hom_π r j A H' f).symm).trans (Category.assoc _ _ _).symm)

end SerrePositivity.Reedy.BoundaryHom
