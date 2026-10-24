module

public import SerrePositivity.InfinityCategories.Core.LimitConeExtension
public import SerrePositivity.InfinityCategories.Core.EquivalenceCylinderFunctorIso

/-!
概要：関手同型に沿って頂点を保つ極限錐の輸送。
方針：可逆円柱の各端点への制限を同値として扱う。
規約：図式の形状には quasicategory 性を要求しない。
使われ方：Cat_∞ の path 置換から元の関手への引き戻しの存在。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：同値な部分形状上の極限錐を頂点を保って全体へ延長できる。
方針：slice の制限の trivial Kan fibration 性で指定錐を持ち上げる。
規約：部分錐全体と頂点を等号で保持する。
使われ方：図式の同型を表す可逆円柱上の極限錐の延長。 -/
lemma exists_limitCone_extension_of_precompositionEquivalence {K L X : SSet.{u}}
    [Quasicategory X] (p : K ⟶ X) (f : L ⟶ K) [Mono f]
    (hf : IsPrecompositionEquivalence f) (d : JoinCone (f ≫ p)) (hd : IsLimitCone d) :
    ∃ c : JoinCone p, IsLimitCone c ∧ restrictJoinCone c f = d ∧ c.vertex = d.vertex := by
  have := sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence p f hf
  exact exists_limitCone_extension_of_trivialRestriction p f d hd
/-- 概要：同型な図式の指定極限錐を同じ頂点の極限錐へ輸送できる。
方針：同型を可逆円柱に延長し、一端から錐を延長して他端へ制限する。
規約：頂点は厳密に保持し、全錐の等号は要求しない。
使われ方：Cat_∞ の元の cospan の極限錐の構成。 -/
lemma exists_limitCone_of_functorIso {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (e : FunctorIso p q) (d : JoinCone q) (hd : IsLimitCone d) :
    ∃ c : JoinCone p, IsLimitCone c ∧ c.vertex = d.vertex := by
  obtain ⟨H, h₀, h₁⟩ := exists_equivalenceCylinder_extension_of_functorIso e
  subst p
  subst q
  have hext := exists_limitCone_extension_of_precompositionEquivalence H
    (equivalenceCylinderEndpoint K true)
    (isPrecompositionEquivalence_equivalenceCylinderEndpoint K true)
  obtain ⟨c, hc, _, hv⟩ := hext d hd
  have := sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence H
    (equivalenceCylinderEndpoint K false)
    (isPrecompositionEquivalence_equivalenceCylinderEndpoint K false)
  have hr : IsLimitCone (restrictJoinCone c (equivalenceCylinderEndpoint K false)) :=
    ((qCatEquivalenceOfTrivialKanFibration
      (sliceOverRestrict H (equivalenceCylinderEndpoint K false))).isTerminalVertex_iff c).1 hc
  have hr' : ∃ c₀ : JoinCone (equivalenceCylinderEndpoint K false ≫ H),
      IsLimitCone c₀ ∧ c₀.vertex = d.vertex :=
    ⟨restrictJoinCone c _, hr, (restrictJoinCone_vertex c _).trans hv⟩
  exact hr'

end SerrePositivity.InfinityCategories.F2
