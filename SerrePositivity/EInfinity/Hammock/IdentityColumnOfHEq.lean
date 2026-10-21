module

public import SerrePositivity.EInfinity.Hammock.IdentityColumn

/-!
# 元の射の異種恒等性から恒等列を回収する

概要：列の両端と同じ対象への同定、元の射の恒等射との異種等式から恒等列を得る。
方針：列の向きに沿って隣接頂点を同定し、射の等式移送を消す。
規約：局所化後の恒等性は使用しない。
使われ方：元の右置換の実際の中央列が挿入の像に入ることの証明。
-/

@[expose] public section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : Word} {X Y E : C}

lemma IdentityColumn.of_heq_id (R : Zigzag W w X Y) (j : Fin w.length)
    (hs : R.vertex (w.source j) = E) (ht : R.vertex (w.target j) = E)
    (ha : HEq (R.arrow j) (𝟙 E)) : IdentityColumn R j := by
  have hv : R.vertex j.castSucc = R.vertex j.succ := by
    cases hd : w.direction j with
    | forward => simpa only [Word.source, Word.target, hd] using hs.trans ht.symm
    | backward => simpa only [Word.source, Word.target, hd] using ht.trans hs.symm
  refine ⟨hv, ?_⟩
  have h := (conj_eqToHom_iff_heq _ _ hs ht).2 ha
  simpa only [Category.id_comp, eqToHom_trans] using h

end SerrePositivity.EInfinity.Hammock
