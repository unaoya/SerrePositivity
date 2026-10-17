module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ElementsFinite
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexFinite
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# 単体圏の逆射が誘導する単体的集合の写像は単射となる

## 概要
単体圏の逆射が誘導する単体的集合の写像は単射となる。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
圏の射列を各単体として評価し、自然変換や端点の射を明示する。
単体ごとの合成と端点の式を照合して、全体の写像を得る。

## 規約と注意
宇宙・境界・比較射は各宣言に指定されたものを用いる。
対象ごとの選択から自然性や厳密な合成則を暗黙には推論しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0557][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0557
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Finite Reedy boundary indices for an arbitrarily large simplicial set

A fixed simplex has only finitely many direct faces and inverse quotients.
All labels are forced by their simplex operators. Neither the whole set
of simplices nor the nerve category is required to be small or finite.
-/

@[expose] public section
universe w vC uC
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite

namespace SerrePositivity.SimplicialModel.SimplexIndexFinite
variable (X : SSet.{w})

abbrev reedy := (Reedy.elementsReedy X Reedy.simplexOp).op

/-- 単体圏の逆射が誘導する単体的集合の写像は単射となる。

宇宙・境界・比較射は各宣言に指定されたものを用いる。
圏の射列を各単体として評価し、自然変換や端点の射を明示する。
単体ごとの合成と端点の式を照合して、全体の写像を得る。
-/
lemma map_inverse_injective {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j)
    (hf : Reedy.simplexInverse.op f) : Function.Injective (X.map f) := by
  have : Epi f.unop := hf
  have : IsSplitEpi f.unop := isSplitEpi_of_epi f.unop
  have : IsSplitMono f := IsSplitMono.mk'
    ((IsSplitEpi.exists_splitEpi (f := f.unop)).some.op)
  have : Mono (X.map f) := inferInstance
  exact (mono_iff_injective (X.map f)).mp inferInstance

instance latchingIndex_finite (s : X.Elementsᵒᵖ) : Finite (Reedy.LatchingIndex (reedy X) s) :=
  Finite.of_equiv (Reedy.MatchingIndex (Reedy.elementsReedy X Reedy.simplexOp) s.unop)
    (Reedy.latchingOpObjEquiv (Reedy.elementsReedy X Reedy.simplexOp) s.unop).symm

instance matchingIndex_finite (s : X.Elementsᵒᵖ) : Finite (Reedy.MatchingIndex (reedy X) s) := by
  have : Finite (Reedy.LatchingIndex (Reedy.elementsReedy X Reedy.simplexOp) s.unop) :=
    Reedy.elementsLatchingIndex_finite X Reedy.simplexOp (map_inverse_injective X) s.unop
  exact Finite.of_equiv (Reedy.LatchingIndex (Reedy.elementsReedy X Reedy.simplexOp) s.unop)
    (Reedy.matchingOpObjEquiv (Reedy.elementsReedy X Reedy.simplexOp) s.unop).symm

instance indexHom_finite (s t : X.Elementsᵒᵖ) : Finite (s ⟶ t) :=
  Finite.of_injective (fun f : s ⟶ t => f.unop.hom.unop) (by
    intro f g h
    exact Quiver.Hom.unop_inj (Functor.Elements.hom_ext (Quiver.Hom.unop_inj h)))

instance latchingHom_finite (s : X.Elementsᵒᵖ) (q q' : Reedy.LatchingIndex (reedy X) s) :
    Finite (q ⟶ q') :=
  Finite.of_injective (fun f : q ⟶ q' => f.hom.left) (by
    intro f g h
    apply ObjectProperty.hom_ext
    exact Over.OverMorphism.ext h)

instance matchingHom_finite (s : X.Elementsᵒᵖ) (q q' : Reedy.MatchingIndex (reedy X) s) :
    Finite (q ⟶ q') :=
  Finite.of_injective (fun f : q ⟶ q' => f.hom.right) (by
    intro f g h
    apply ObjectProperty.hom_ext
    exact Under.UnderMorphism.ext h)

instance latchingIndex_finCategory (s : X.Elementsᵒᵖ) :
    FinCategory (ULiftHom.{w} (Reedy.LatchingIndex (reedy X) s)) where
  fintypeObj := by
    letI : Fintype (Reedy.LatchingIndex (reedy X) s) := Fintype.ofFinite _
    exact Fintype.ofEquiv _ ULiftHom.objEquiv
  fintypeHom a b := by
    change Fintype (ULift.{w} (a.objDown ⟶ b.objDown))
    letI : Fintype (a.objDown ⟶ b.objDown) := Fintype.ofFinite _
    infer_instance

instance matchingIndex_finCategory (s : X.Elementsᵒᵖ) :
    FinCategory (ULiftHom.{w} (Reedy.MatchingIndex (reedy X) s)) where
  fintypeObj := by
    letI : Fintype (Reedy.MatchingIndex (reedy X) s) := Fintype.ofFinite _
    exact Fintype.ofEquiv _ ULiftHom.objEquiv
  fintypeHom a b := by
    change Fintype (ULift.{w} (a.objDown ⟶ b.objDown))
    letI : Fintype (a.objDown ⟶ b.objDown) := Fintype.ofFinite _
    infer_instance

variable {C : Type uC} [Category.{vC} C]

instance latchingHasLimits [HasFiniteLimits C] (s : X.Elementsᵒᵖ) :
    HasLimitsOfShape (Reedy.LatchingIndex (reedy X) s) C := by
  let e : Reedy.LatchingIndex (reedy X) s ≌
      ULiftHom.{w} (Reedy.LatchingIndex (reedy X) s) := ULiftHom.equiv
  exact hasLimitsOfShape_of_equivalence e.symm

instance latchingHasColimits [HasFiniteColimits C] (s : X.Elementsᵒᵖ) :
    HasColimitsOfShape (Reedy.LatchingIndex (reedy X) s) C := by
  let e : Reedy.LatchingIndex (reedy X) s ≌
      ULiftHom.{w} (Reedy.LatchingIndex (reedy X) s) := ULiftHom.equiv
  exact hasColimitsOfShape_of_equivalence e.symm

instance matchingHasLimits [HasFiniteLimits C] (s : X.Elementsᵒᵖ) :
    HasLimitsOfShape (Reedy.MatchingIndex (reedy X) s) C := by
  let e : Reedy.MatchingIndex (reedy X) s ≌
      ULiftHom.{w} (Reedy.MatchingIndex (reedy X) s) := ULiftHom.equiv
  exact hasLimitsOfShape_of_equivalence e.symm

instance matchingHasColimits [HasFiniteColimits C] (s : X.Elementsᵒᵖ) :
    HasColimitsOfShape (Reedy.MatchingIndex (reedy X) s) C := by
  let e : Reedy.MatchingIndex (reedy X) s ≌
      ULiftHom.{w} (Reedy.MatchingIndex (reedy X) s) := ULiftHom.equiv
  exact hasColimitsOfShape_of_equivalence e.symm

end SerrePositivity.SimplicialModel.SimplexIndexFinite
