module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.EnrichedFunctorSmallness

/-!
概要：頂点の対象を固定した coherent nerve への写像の小ささ。
方針：各単体の対象作用をその頂点の像から求め、固定対象の豊穣関手として符号化する。
規約：始域は各次数で u に小さく、標的の Hom は宇宙 u。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coslice による unstraightening の小さい代表の構成。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：coherent nerve への写像の各単体の対象は、その頂点の像から求まる。
方針：指定頂点への定値な単体圏の射に対する自然性を評価する。
規約：i は coherent nerve の thickening の対象。
使われ方：Kerodon §2.4.3（Tag 00KM）、coherent な単体の対象作用を固定する計算。 -/
lemma coherentMap_simplex_obj {D : Type v} [Category.{u} D] [SimplicialCategory D]
    {X : SSet.{max u v}} (f : X ⟶ SimplicialNerve D)
    {n : SimplexCategoryᵒᵖ} (s : X.obj n)
    (i : SimplicialThickening (ULift.{u} (Fin (n.unop.len + 1)))) :
    (f.app n s).obj i = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject
      (f.app (Opposite.op ⦋0⦌)
        (X.map (SimplexCategory.const ⦋0⦌ n.unop i.as.down).op s)) := by
  have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject
    (congrArg (fun a ↦ a s) (f.naturality (SimplexCategory.const ⦋0⦌ n.unop i.as.down).op))
  exact h.symm

/-- 概要：頂点の対象を固定した coherent な写像を各単体の固定対象の豊穣関手へ写す。
方針：写像の自然性で各対象の値を頂点の指定値に移す。
規約：符号化は単体間の自然性の証明を保持しない。
使われ方：Kerodon §2.4.3（Tag 00KM）、coherent な写像の小さい符号化。 -/
def coherentMapFixedVertexCode {D : Type v} [Category.{u} D] [SimplicialCategory D]
    {X : SSet.{max u v}} (obj : X _⦋0⦌ → D)
    (f : {f : X ⟶ SimplicialNerve D //
      ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (f.app (Opposite.op ⦋0⦌) x) = obj x}) :
    ∀ (n : SimplexCategoryᵒᵖ) (s : X.obj n),
      {F : EnrichedFunctor SSet.{u}
        (SimplicialThickening (ULift.{u} (Fin (n.unop.len + 1)))) D //
        F.obj = fun i ↦ obj (X.map
          (SimplexCategory.const ⦋0⦌ n.unop i.as.down).op s)} :=
  fun n s ↦ ⟨f.val.app n s, funext fun i ↦
    (coherentMap_simplex_obj f.val s i).trans (f.property _)⟩

/-- 概要：頂点を固定した coherent な写像の符号化は単射。
方針：各単体の豊穣関手の等式から単体集合の射の外延性を使う。
規約：始域と標的に充填性を仮定しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、固定頂点の写像の小ささの検証。 -/
lemma coherentMapFixedVertexCode_injective
    {D : Type v} [Category.{u} D] [SimplicialCategory D]
    {X : SSet.{max u v}} (obj : X _⦋0⦌ → D) :
    Function.Injective (coherentMapFixedVertexCode obj) := by
  intro f g h
  apply Subtype.ext
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  exact congrArg Subtype.val (congrFun (congrFun h n) s)

/-- 概要：各次数で小さい始域からの、頂点の対象を固定した coherent な写像の型は小さい。
方針：各次数の固定対象の豊穣関手の小ささを関数の型へ拡張し、単射で引き戻す。
規約：標的の対象全体の小ささは要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、普遍的な pointed-space 射影の次数ごとの小ささ。 -/
instance coherentMap_fixedVertices_small
    {D : Type v} [Category.{u} D] [SimplicialCategory D]
    {X : SSet.{max u v}} [∀ n, Small.{u} (X.obj n)] (obj : X _⦋0⦌ → D) :
    Small.{u} {f : X ⟶ SimplicialNerve D //
      ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (f.app (Opposite.op ⦋0⦌) x) = obj x} :=
  small_of_injective (coherentMapFixedVertexCode_injective obj)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
