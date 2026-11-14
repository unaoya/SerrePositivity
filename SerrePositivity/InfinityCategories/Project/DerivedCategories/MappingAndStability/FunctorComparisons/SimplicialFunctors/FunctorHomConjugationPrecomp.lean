module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.FunctorHomTypedWhiskerAlgebra
/-!
概要：指定同型の逆と任意全関手射の共役式を、同じ入力前合成へ移送する。
方針：端点を明示して射の一致を保ち、前合成の関手性だけを使う。
規約：指定値を保持し射の可逆性を追加しない。使われ方：変更同型の公開式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
lemma functorIso_inv_heq_of_endpoint_heq {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (hf : f = f') (hg : g = g')
    (he : HEq e e') : HEq e.inv e'.inv := by
  subst f' g'
  cases eq_of_heq he
  rfl
lemma functorHom_conjugation_precomp {X Y Z : SSet.{u}}
    {f g f' g' : X ⟶ Y} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (p : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f f')
    (q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g g') (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f' g')
    (h : c.hom = p.hom ≫ a ≫ q.inv) (J : Z ⟶ X) :
    (c.precomp J).hom = (p.precomp J).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f' g' J a ≫ (q.precomp J).inv := by
  have hh := congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f g J k) h
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_hom_typed] using! hh
end SerrePositivity.InfinityCategories.Project.DerivedCategories
