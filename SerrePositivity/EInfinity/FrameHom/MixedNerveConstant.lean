module
public import SerrePositivity.EInfinity.FrameHom.MixedNerveNatTrans

/-!
概要：対象と Hom の宇宙が異なる通常圏の定値図式を同じ定値単体写像に同定する。
方針：元の nerve の全射列で定値関手の作用を比較する。
規約：元の指定頂点を保つ。使われ方：全正規化単体屋根の両端の定値図式への照合。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.MixedNerve
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
variable (I C : Type (u + 1)) [Category.{u} I] [Category.{u} C]

lemma nerveMap_const (x : C) :
    nerveMap ((Functor.const I).obj x) = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j f => ?_)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end SerrePositivity.EInfinity.FrameHom.MixedNerve
