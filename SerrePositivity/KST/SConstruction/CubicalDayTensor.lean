module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.SConstruction.ConcreteCubeMonoidal
public import SerrePositivity.KST.SConstruction.CubicalPresheaf
public import Mathlib.CategoryTheory.Monoidal.DayConvolution.DayFunctor
public import Mathlib.CategoryTheory.Monoidal.Opposite
public import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-! # 具体的な連結積による cubical sets の Day tensor
概要：元の具体的立方体の連結積を、全 cubical sets 上のモノイダル構造へ延長する。
方針：Type の余極限と直積の余極限保存に、点ごとの左 Kan 延長の Day 構成を適用する。
規約：前層の点ごとの直積と区別する型を使う。使われ方：cubical rigidification の合成。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open scoped MonoidalCategory.ExternalProduct

/-- 連結積に沿う Day tensor を持つ元の cubical sets。 -/
abbrev CubicalDaySet := DayFunctor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ (Type u)

/-- Day tensor は全 cubical sets 上で結合・単位の coherent 法則を満たす。 -/
@[instance_reducible]
def cubicalDayMonoidal : MonoidalCategory CubicalDaySet.{u} := inferInstance

/-- 元の cubical sets と、Day tensor を使う型との間の同じ前層の圏同値。 -/
def cubicalDayEquivalence : CubicalDaySet.{u} ≌ CubicalSet.{u} :=
  DayFunctor.equiv _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ (Type u)

/-- 元の二つの cubical sets の連結に沿う Day tensor。 -/
def cubicalDayTensor (K L : CubicalSet.{u}) : CubicalSet.{u} :=
  ((DayFunctor.mk K) ⊗ (DayFunctor.mk L)).functor

/-- Day tensor を元の二つの cell から生成する左 Kan 延長の単位。 -/
def cubicalDayTensorUnit (K L : CubicalSet.{u}) :
    K ⊠ L ⟶ tensor _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ ⋙ cubicalDayTensor K L :=
  DayFunctor.η (DayFunctor.mk K) (DayFunctor.mk L)

/-- 元の Day tensor は仮定なしに左 Kan 延長の普遍性を持つ。 -/
instance cubicalDayTensor_isLeftKanExtension (K L : CubicalSet.{u}) :
    (cubicalDayTensor K L).IsLeftKanExtension (cubicalDayTensorUnit K L) := by
  change ((DayFunctor.mk K) ⊗ (DayFunctor.mk L)).functor.IsLeftKanExtension
    (DayFunctor.η (DayFunctor.mk K) (DayFunctor.mk L))
  infer_instance

/-- 元の二つの cubical sets の射の Day tensor。 -/
def cubicalDayTensorMap {K K' L L' : CubicalSet.{u}} (f : K ⟶ K') (g : L ⟶ L') :
    cubicalDayTensor K L ⟶ cubicalDayTensor K' L' :=
  (@tensorHom CubicalDaySet.{u} _ _ (DayFunctor.mk K) (DayFunctor.mk K')
    (DayFunctor.mk L) (DayFunctor.mk L') (DayFunctor.Hom.mk f) (DayFunctor.Hom.mk g)).natTrans

/-- Day tensor の元の左 Kan 延長の普遍性による射の判定。 -/
lemma cubicalDayTensor_hom_ext {K L M : CubicalSet.{u}}
    {f g : cubicalDayTensor K L ⟶ M}
    (h : cubicalDayTensorUnit K L ≫ Functor.whiskerLeft _ f =
      cubicalDayTensorUnit K L ≫ Functor.whiskerLeft _ g) : f = g :=
  Functor.hom_ext_of_isLeftKanExtension _ (cubicalDayTensorUnit K L) _ _ h

end SerrePositivity.KST.SConstruction

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "2.2.6.17" (partial := special) "仮定：通常圏の立方体添字と集合値の前層（Lean が強い：具体的な通常圏を固定）。結論：関手圏の Day モノイダル構造と、テンソルを元のテンソルに沿う左 Kan 延長とする普遍性（この場合に一致）。一般の関手 ∞ operad とその対称構造は型に含まれない。"] _root_.SerrePositivity.KST.SConstruction.cubicalDayMonoidal
attribute [cite HA "2.2.6.17" (partial := special) "仮定：通常圏の立方体添字と集合値の前層（Lean が強い：具体的な通常圏を固定）。結論：関手圏の Day モノイダル構造と、テンソルを元のテンソルに沿う左 Kan 延長とする普遍性（この場合に一致）。一般の関手 ∞ operad とその対称構造は型に含まれない。"] _root_.SerrePositivity.KST.SConstruction.cubicalDayTensor_isLeftKanExtension
