module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams
public import Mathlib.CategoryTheory.Category.ULift

/-!
概要：小圏の strict な図式を、サイズを明示した coherent nerve の図式にする。
方針：添字圏の対象と射を AsSmall で持ち上げ、nerve の ULift との厳密な同型を使う。
規約：Hom の宇宙 u、対象の宇宙 v、図式の始域は ULift N(I) : SSet.{max u v}。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の strict な図式の表示。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {I : Type u} [SmallCategory I]

/-- 概要：小圏の nerve の持ち上げを、持ち上げた小圏の nerve に送る。
方針：単体の ULift を外し、合成可能射列に AsSmall.up を後合成する。
規約：対象と射のサイズを同時に v へ持ち上げる。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の図式のサイズの調整。 -/
def nerveAsSmallUp (I : Type u) [SmallCategory I] :
    (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ nerve (AsSmall.{v} I) where
  app _ := ↾fun s ↦ s.down ⋙ AsSmall.up
  naturality _ _ _ := rfl

/-- 概要：持ち上げた小圏の nerve を、元の nerve の ULift に戻す。
方針：合成可能射列に AsSmall.down を後合成して ULift に入れる。
規約：標的の単体は元の宇宙の射列を一つ持つ。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の図式のサイズの調整の逆。 -/
def nerveAsSmallDown (I : Type u) [SmallCategory I] :
    nerve (AsSmall.{v} I) ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve I) where
  app _ := ↾fun s ↦ ULift.up (s ⋙ AsSmall.down)
  naturality _ _ _ := rfl

/-- 概要：nerve の ULift は対象と射を持ち上げた圏の nerve と厳密に同型。
方針：AsSmall の二つの関手の合成を各単体で計算する。
規約：圏同値からの弱い比較だけではなく SSet の同型を使う。
使われ方：HTT 4.2.4.1 の双対の錐の形を同じ宇宙に置く。 -/
def nerveAsSmallIso (I : Type u) [SmallCategory I] :
    (SSet.uliftFunctor.{v, u}).obj (nerve I) ≅ nerve (AsSmall.{v} I) where
  hom := nerveAsSmallUp I
  inv := nerveAsSmallDown I
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- 概要：nerve の持ち上げの同型は元の対象の頂点を対応する持ち上げた対象に写す。
方針：零次の合成可能射列を唯一の対象で比較する。
規約：始域の点の射も大きい宇宙に置く。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の錐の各脚の制限。 -/
lemma nerveAsSmallIso_vertex (I : Type u) [SmallCategory I] (i : I) :
    SSet.yonedaEquiv.symm (ULift.up (ComposableArrows.mk₀ i)) ≫ (nerveAsSmallIso I).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (AsSmall.up.obj i) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact ComposableArrows.ext₀ rfl

/-- 概要：全体のサイズが一致する二つの圏の間で、関手から nerve の射を作る。
方針：各合成可能射列に通常の関手を後合成する。
規約：始域はサイズ max u v の小圏、標的は対象 v・射 u の圏。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の持ち上げた添字圏の錐の表示。 -/
def resizedNerveMap {J : Type (max u v)} [SmallCategory J] {C : Type v} [Category.{u} C]
    (F : J ⥤ C) : nerve J ⟶ nerve C where
  app _ := ↾fun s ↦ s ⋙ F
  naturality _ _ _ := rfl

/-- 概要：持ち上げた小圏の関手を前合成した nerve の射は通常の射列の合成に一致する。
方針：各単体の関手の合成を展開する。
規約：前合成の二つの小圏のサイズは max u v。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の錐の図式への制限。 -/
lemma resizedNerveMap_precomp {J K : Type (max u v)} [SmallCategory J] [SmallCategory K]
    {C : Type v} [Category.{u} C] (F : J ⥤ K) (G : K ⥤ C) :
    nerveMap F ≫ resizedNerveMap G = resizedNerveMap (F ⋙ G) := rfl

/-- 概要：サイズを調整した nerve の射は元の関手の対象への作用と一致する。
方針：零次の合成可能射列を唯一の対象で比較する。
規約：恒等射の像を定義的な恒等射とは扱わない。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の錐の頂点の計算。 -/
lemma resizedNerveMap_vertex {J : Type (max u v)} [SmallCategory J]
    {C : Type v} [Category.{u} C] (F : J ⥤ C) (j : J) :
    (resizedNerveMap F).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ j) =
      ComposableArrows.mk₀ (F.obj j) :=
  ComposableArrows.ext₀ rfl

/-- 概要：サイズを調整した nerve の射は通常の射をその関手による像の辺に写す。
方針：一次の合成可能射列を対象と唯一の生成射で比較する。
規約：通常の nerve の mk₁ に関する厳密な等式。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の錐の成分の回収。 -/
lemma resizedNerveMap_edge {J : Type (max u v)} [SmallCategory J]
    {C : Type v} [Category.{u} C] (F : J ⥤ C) {i j : J} (f : i ⟶ j) :
    (resizedNerveMap F).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁ (F.map f) :=
  ComposableArrows.ext₁ rfl rfl (by simp [resizedNerveMap])

/-- 概要：strict な通常の図式から coherent nerve の図式を作る。
方針：持ち上げた添字圏の nerve へ移し、図式を後合成して F1 の標準射を使う。
規約：始域は明示的な ULift N(I)、追加の局所 Kan 性は定義に不要。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の p = N(F)。 -/
noncomputable def strictCoherentDiagram {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (F : I ⥤ C) :
    (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C :=
  (nerveAsSmallIso I).hom ≫ resizedNerveMap (AsSmall.down ⋙ F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C

/-- 概要：strict な図式の頂点は元の対象の coherent nerve の頂点になる。
方針：AsSmall と通常の nerve の標準射を零単体で評価する。
規約：添字 i は元の小圏の対象。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の錐の頂点と図式の対象の照合。 -/
lemma strictCoherentDiagram_vertex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (i : I) :
    (strictCoherentDiagram F).app (Opposite.op ⦋0⦌) (ULift.up (ComposableArrows.mk₀ i)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj i) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object
    ((strictCoherentDiagram F).app (Opposite.op ⦋0⦌) (ULift.up (ComposableArrows.mk₀ i)))).symm

/-- 概要：strict な図式の coherent 表示は通常の添字圏の関手による制限と可換。
方針：各単体の合成可能射列に対する後合成の順序を比較する。
規約：二つの添字圏はともに宇宙 u の小圏。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の部分図式・塔・引き戻しの形への制限。 -/
lemma strictCoherentDiagram_precomp {J : Type u} [SmallCategory J]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (G : I ⥤ J) (F : J ⥤ C) :
    (SSet.uliftFunctor.{v, u}).map (nerveMap G) ≫ strictCoherentDiagram F =
      strictCoherentDiagram (G ⋙ F) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
