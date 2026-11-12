module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence

/-!
概要：充満忠実性による元の頂点同型の逆像が、指定された像と一意性を保つことを示す。
方針：ホモトピー圏の同じ充満忠実な関手の逆像の公式を使う。
規約：逆像や指定同型を再選択しない。使われ方：native 比較の指定正方形の反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の充満忠実な関手の同型の逆像は、元の指定同型そのものへ写る。 -/
lemma vertexIso_map_preimage {A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
    {f : A ⟶ B} (hf : IsFullyFaithful f) {x y : A _⦋0⦌}
    (e : VertexIso (f.app _ x) (f.app _ y)) :
    VertexIso.map (hf.preimageVertexIso e) f = e := by
  apply Iso.ext
  exact hf.toHoFullyFaithful.map_preimage
    (X := SSet.HomotopyCategory.mk x) (Y := SSet.HomotopyCategory.mk y) e.hom

/-- 元の充満忠実な関手は、同じ実両端間の指定頂点同型の値を反映する。 -/
lemma vertexIso_map_injective {A B : SSet.{u}} [Quasicategory A] [Quasicategory B]
    {f : A ⟶ B} (hf : IsFullyFaithful f) {x y : A _⦋0⦌} :
    Function.Injective (fun e : VertexIso x y => VertexIso.map e f) := by
  intro e e' he
  apply Iso.ext
  exact hf.toHoFullyFaithful.map_injective (congrArg Iso.hom he)

end SerrePositivity.InfinityCategories.F2
