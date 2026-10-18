module

public import SerrePositivity.InfinityCategories.F1B.WeakHomotopyInverse

/-!
概要：恒等射から合成へ向くホモトピー逆データも弱ホモトピー同値を与える。
方針：Kan 標的への前合成で得る自然同型を逆にする。
規約：元のホモトピーを単体的に逆向きへ反転する必要はない。
使われ方：終対象を持つ単体集合の弱可縮性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：恒等射から両合成へのホモトピーがあれば弱ホモトピー同値。
方針：全 Kan 標的への前合成でホモトピーを可逆二胞体にし、その逆を使う。
規約：元の二対象の Kan 性や quasicategory 性を要求しない。
使われ方：Kerodon Proposition 3.1.7.13、終対象による収縮。 -/
lemma isWeakHomotopyEquivalence_of_reverseHomotopyInverse {A B : SSet.{u}}
    (f : A ⟶ B) (g : B ⟶ A) (H : SSet.Homotopy (𝟙 A) (f ≫ g))
    (K : SSet.Homotopy (𝟙 B) (g ≫ f)) : IsWeakHomotopyEquivalence f := by
  intro Z hZ
  have he : IsQCatEquivalence ((pre f).app Z) := by
    refine ⟨(pre g).app Z, ⟨?_⟩, ⟨?_⟩⟩
    · simpa only [pre_map, NatTrans.comp_app, pre_id, NatTrans.id_app] using
        (functorIsoPrecompositionOfHomotopy_kan K Z).symm
    · simpa only [pre_map, NatTrans.comp_app, pre_id, NatTrans.id_app] using
        (functorIsoPrecompositionOfHomotopy_kan H Z).symm
  exact he.isSimplicialHomotopyEquivalence.mapPiZero_bijective

end SerrePositivity.InfinityCategories
