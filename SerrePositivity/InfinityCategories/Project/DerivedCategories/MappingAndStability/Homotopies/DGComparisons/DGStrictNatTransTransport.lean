module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGStrictNatTransAlgebra
/-!
概要：元の二経路の比較を両射影へ送り、同じ全厳密変換へ同定する。
方針：全 Hom 写像の等式と閉零成分を、関手の厳密等式に沿って照合する。
規約：恒等と元の入力変換を全体として回収。使われ方：指定比較の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
lemma dgStrictNatTrans_heq_of_val
    {R : Type u} [CommRing R] {C : Type v} {E : Type w}
    [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
    {F G F' G' : DGFunctor R C E} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F' G')
    (hF : F = F') (hG : G = G') (h : ∀ x, HEq (η.app x).val (θ.app x).val) :
    HEq η θ := by
  subst F' G'
  apply heq_of_eq
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_ext
  intro x
  apply Subtype.ext
  exact eq_of_heq (h x)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
