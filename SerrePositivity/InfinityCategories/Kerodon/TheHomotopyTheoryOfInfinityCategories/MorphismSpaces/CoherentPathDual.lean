module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomEquivalence
public import Mathlib.CategoryTheory.Enriched.Opposite

/-!
概要：包含順序の coherent path を順序双対で反転する。
方針：同じ部分集合を使って二端点を交換し、豊穣合成では二つの path の順序を交換する。
規約：path の包含の向きは変えず、基礎の線形順序を双対にする。
使われ方：Kerodon §4.6.7（Tag 01LA） の左右の写像空間の向き、HTT 4.2.4.1 の係数比較の準備。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet SimplicialThickening
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：coherent path を同じ部分集合のまま順序双対の逆向きの path にする。
方針：二端点の所属と上下界の条件を交換する。
規約：包含関係は元と同じ向きである。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の coherent 図式の path の表示。 -/
def coherentPathDual {J : Type u} [LinearOrder J] {i j : J} (P : Path i j) :
    Path (OrderDual.toDual j) (OrderDual.toDual i) where
  I := P.I
  left := P.right
  right := P.left
  left_le k hk := P.le_right k hk
  le_right k hk := P.left_le k hk

/-- 概要：coherent path の順序双対への反転は二回適用すると元に戻る。
方針：部分集合が変わらないことを使う。
規約：二重の順序双対は元の型と定義的に一致する。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の比較の往復則。 -/
lemma coherentPathDual_dual {J : Type u} [LinearOrder J] {i j : J} (P : Path i j) :
    coherentPathDual (coherentPathDual P) = P := by
  apply SimplicialThickening.Path.ext
  rfl

/-- 概要：coherent path の反転は包含順序の圏の関手になる。
方針：包含を同じ包含として写す。
規約：元の path の両端 i,j は固定する。
使われ方：Kerodon §4.6.7（Tag 01LA） の豊穣 Hom の反対の比較の定義。 -/
def coherentPathDualFunctor {J : Type u} [LinearOrder J] (i j : J) :
    Path i j ⥤ Path (OrderDual.toDual j) (OrderDual.toDual i) where
  obj := coherentPathDual
  map f := ⟨⟨⟨f.1.1.1⟩⟩⟩

/-- 概要：path の反転は恒等 path を恒等 path に写す。
方針：一点集合としての恒等 path を比較する。
規約：SimplicialThickening の恒等射を使う。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の豊穣関手の単位則。 -/
lemma coherentPathDual_id {J : Type u} [LinearOrder J] (i : J) :
    coherentPathDual (𝟙 (⟨i⟩ : SimplicialThickening J)) =
      𝟙 (⟨OrderDual.toDual i⟩ : SimplicialThickening Jᵒᵈ) := by
  apply SimplicialThickening.Path.ext
  rfl

/-- 概要：path の反転は合成を逆順の合成に写す。
方針：合成の部分集合が和集合であることと和集合の交換則を使う。
規約：包含順序を反転せず、二つの合成因子の順序を交換する。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の豊穣関手の合成則。 -/
lemma coherentPathDual_comp {J : Type u} [LinearOrder J] {i j k : SimplicialThickening J}
    (P : i ⟶ j) (Q : j ⟶ k) :
    coherentPathDual (P ≫ Q) =
      @CategoryStruct.comp (SimplicialThickening Jᵒᵈ) _
        ⟨OrderDual.toDual k.as⟩ ⟨OrderDual.toDual j.as⟩ ⟨OrderDual.toDual i.as⟩
        (coherentPathDual Q) (coherentPathDual P) := by
  apply SimplicialThickening.Path.ext
  exact Set.union_comm _ _

/-- 概要：simplicial thickening は順序双対の thickening の反対へ豊穣関手を持つ。
方針：対象を順序双対へ移し、Hom は path の反転の nerve で与える。
規約：反対の豊穣合成には SSet の対称性を使う。
使われ方：Kerodon §4.6.7（Tag 01LA） の反対の coherent nerve と左右の Hom の比較。 -/
def coherentThickeningDual (J : Type u) [LinearOrder J] :
    EnrichedFunctor SSet (SimplicialThickening J) (SimplicialThickening Jᵒᵈ)ᵒᵖ where
  obj i := Opposite.op ⟨OrderDual.toDual i.as⟩
  map i j := nerveMap (coherentPathDualFunctor i.as j.as)
  map_id i := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro t
    apply CategoryTheory.Functor.ext (fun _ => ?_)
    exact coherentPathDual_id i.as
  map_comp i j k := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    apply CategoryTheory.Functor.ext (fun a => ?_)
    exact coherentPathDual_comp (P.obj a) (Q.obj a)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
