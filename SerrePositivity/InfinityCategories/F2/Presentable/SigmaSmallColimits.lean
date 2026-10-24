module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaReflectorAdjunction
public import SerrePositivity.InfinityCategories.F2.Presentable.LeftAdjointCoconePreservation
public import SerrePositivity.InfinityCategories.F2.Presentable.CoproductRealizationColimits

/-!
概要：専用反映を使い P_Σ の小余積と全小余極限を構成する。
方針：前層の小余積を反映し、可逆な余単位で元の図式を回収する。
規約：一般 Bousfield 局所化の存在を使わない。
使われ方：P_Σ 上の全小余極限保存判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：有限余積を持つ底の P_Σ は小余積を持つ。
方針：周囲の前層の指定小余積を左随伴で反映し、余単位同型で戻す。
規約：元の小離散図式を結論に保持する。
使われ方：全小余極限存在と保存判定。 -/
lemma sigma_hasSmallCoproducts {C : SSet.{u}} [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p) :
    HasSmallCoproducts (SigmaPresheafInfinity C) := by
  obtain ⟨L, β, hβ⟩ := sigma_exists_reflectorLeftKan hC
  obtain ⟨ε, hε⟩ := sigmaReflector_exists_counit β hβ
  have := sigmaReflector_counit_isIso β hβ ε hε
  intro I p
  obtain ⟨c, hc⟩ := presheaf_hasSmallColimits C (nerve (Discrete I))
    (p ≫ sigmaPresheafInfinityInclusion C)
  have hLc := mapJoinCocone_isColimit_of_adjunction_of_quasicategoryShape
    (sigmaReflectorAdjunction β hβ) c hc
  have e : FunctorIso ((p ≫ sigmaPresheafInfinityInclusion C) ≫ L) p := by
    simpa only [Category.assoc, Category.comp_id] using FunctorIso.precomp (asIso ε) p
  exact (hasColimit_iff_of_functorIso e).mp ⟨mapJoinCocone L c, hLc⟩

/-- 概要：有限余積を持つ底の P_Σ は全小余極限を持つ。
方針：構成した小余積と既存の幾何学的実現から一般構成を使う。
規約：任意の小さい単体集合形状を扱う。
使われ方：全余極限保存の有限余積判定。 -/
lemma sigma_hasSmallColimits {C : SSet.{u}} [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p) :
    HasSmallColimits (SigmaPresheafInfinity C) :=
  hasSmallColimits_of_coproducts_geometricRealizations (sigma_hasSmallCoproducts hC)
    (sigma_hasSmallGeometricRealizations C)

end SerrePositivity.InfinityCategories.F2.Presentable
