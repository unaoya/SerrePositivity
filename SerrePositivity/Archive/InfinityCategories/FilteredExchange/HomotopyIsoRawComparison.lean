module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.HomotopyIsoTransport
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-!
概要：同じ全円柱から作る指定同型は、異なる端点表示でも型付きで一致する。
方針：端点の等式を全円柱の両端評価から明示し、元の指定類の比較を適用する。
規約：同型の HEq から端点等式を取り出さない。使われ方：持ち上げた模型 path の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 三つの射の明示した等式と指定値の一致は、二つの指定同型の合成を保つ。 -/
lemma functorIso_trans_heq_of_heq {A X : SSet.{u}} {f g h f' g' h' : A ⟶ X}
    (a : FunctorIso f g) (b : FunctorIso g h)
    (a' : FunctorIso f' g') (b' : FunctorIso g' h')
    (hf : f = f') (hg : g = g') (hh : h = h') (ha : HEq a a') (hb : HEq b b') :
    HEq (a ≪≫ b) (a' ≪≫ b') := by
  subst f' g' h'
  cases eq_of_heq ha
  cases eq_of_heq hb
  rfl

/-- 同じ raw な全円柱の指定類は、両端評価による補正の下で同じ。 -/
lemma homotopyIso_heq_of_h_eq {A X : SSet.{u}} [KanComplex X]
    {f g f' g' : A ⟶ X} (H : SSet.Homotopy f g) (K : SSet.Homotopy f' g')
    (h : H.h = K.h) :
    HEq (functorIsoOfSimplicialHomotopy H) (functorIsoOfSimplicialHomotopy K) := by
  have hf : f = f' := H.h₀.symm.trans ((congrArg (fun k => SSet.ι₀ ≫ k) h).trans K.h₀)
  have hg : g = g' := H.h₁.symm.trans ((congrArg (fun k => SSet.ι₁ ≫ k) h).trans K.h₁)
  have hi := functorIsoOfEq_of_homotopy_h_eq H K
    (functorIsoOfSimplicialHomotopy H) (functorIsoOfSimplicialHomotopy K) rfl rfl hf hg h
  exact (functorIsoOfEq_heq _ hf hg).symm.trans (heq_of_eq hi)

end SerrePositivity.InfinityCategories.F2
