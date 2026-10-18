module

public import SerrePositivity.InfinityCategories.F1B.WeakHomotopy

/-!
概要：単体的ホモトピー逆から弱ホモトピー同値を得る。
方針：Kan 標的への前合成では任意のホモトピーが可逆な二胞体になることを使う。
規約：元の始域・終域に Kan 性を課さず、元のホモトピーにも可逆性を要求しない。
使われ方：Kerodon Proposition 3.1.7.13、弱可縮な補助模型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：任意のホモトピーは Kan 標的への前合成の自然同型を与える。
方針：前合成を表す単体的射でホモトピーの辺を写し、Kan 性により可逆にする。
規約：H の成分の辺の可逆性は不要。可逆性は Z の Kan 性から得る。
使われ方：Kerodon Proposition 3.1.7.13、ホモトピー逆の反変作用。 -/
noncomputable def functorIsoPrecompositionOfHomotopy_kan {A B : SSet.{u}}
    {f g : A ⟶ B} (H : SSet.Homotopy f g) (Z : SSet.{u}) [KanComplex Z] :
    FunctorIso ((pre f).app Z) ((pre g).app Z) := by
  let e : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom ((ihom B).obj Z)).obj ((ihom A).obj Z)))
      (functorVertex ((pre f).app Z)) (functorVertex ((pre g).app Z)) :=
    (functorEdgeOfSimplicialHomotopy H).map
      ((truncation 2).map (functorPrecompositionMap A B Z))
  exact functorIsoOfSimplicialHomotopy (simplicialHomotopyOfFunctorEdge e)

/-- 概要：実際の単体的ホモトピー逆を持つ任意の射は弱ホモトピー同値。
方針：各 Kan 標的への前合成の逆と両合成の自然同型を構成して π₀ を取る。
規約：元の単体集合は Kan 複体や quasicategory でなくてもよい。
使われ方：Kerodon Proposition 3.1.7.13 の第一の主張。 -/
lemma IsSimplicialHomotopyEquivalence.isWeakHomotopyEquivalence {A B : SSet.{u}}
    {f : A ⟶ B} (hf : IsSimplicialHomotopyEquivalence f) : IsWeakHomotopyEquivalence f := by
  obtain ⟨g, ⟨H⟩, ⟨K⟩⟩ := hf
  intro Z hZ
  have he : IsQCatEquivalence ((pre f).app Z) := by
    refine ⟨(pre g).app Z, ⟨?_⟩, ⟨?_⟩⟩
    · simpa only [pre_map, NatTrans.comp_app, pre_id, NatTrans.id_app] using
        functorIsoPrecompositionOfHomotopy_kan K Z
    · simpa only [pre_map, NatTrans.comp_app, pre_id, NatTrans.id_app] using
        functorIsoPrecompositionOfHomotopy_kan H Z
  exact he.isSimplicialHomotopyEquivalence.mapPiZero_bijective

end SerrePositivity.InfinityCategories
