module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeLeftUnitInvertible
public import SerrePositivity.InfinityCategories.F1B.KanRelativeLeftCanonical
public import SerrePositivity.InfinityCategories.F1B.KanRelativeColimitFunctorIso

/-!
概要：可逆な相対左 Kan 単位から元の関手の標準局所条件を得る。
方針：局所輸送の可逆性と余錐全体の同型による相対余極限の保存を使う。
規約：元の標準余錐と任意の inner U を扱う。
使われ方：相対左 Kan 関手の全部分圏内での厳密化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：可逆な相対左 Kan 単位を持つ関手は標準局所条件を満たす。
方針：局所輸送の同型で U 余極限性を標準余錐へ戻す。
規約：包含の充満忠実性は不要で、指定単位の可逆性を入力する。
使われ方：指定変換の模型から元の関手の頂点条件へ移る。 -/
lemma kanRelativeLeftKanExtension_canonical_of_unit_isIso {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    (δ : K ⟶ C) {F₀ : K ⟶ D} {F : C ⟶ D} (β : SSet.Homotopy F₀ (δ ≫ F))
    (hβ : IsRelativeLeftKanExtension U δ F₀ F β)
    (hi : IsIso (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β))) :
    IsRelativeLeftKanExtendedFrom U δ F := by
  intro c
  obtain ⟨t, ht⟩ := hβ c
  have := kanLeftTransport_isIso_of_unit_isIso t hi
  exact kanIsRelativeColimitCone_of_functorIso U ht
    (asIso (SSet.Truncated.HomotopyCategory.homMk t.edge))

/-- 概要：関手圏の同型は元の標準相対左 Kan 条件を保つ。
方針：標準局所余錐の射への前合成で全余錐の同型を作る。
規約：図式の各点の同型を独立に選ばない。
使われ方：元と像を固定した同値による図式の厳密化。 -/
lemma kanIsRelativeLeftKanExtendedFrom_of_functorIso {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    (δ : K ⟶ C) {F G : C ⟶ D} (e : FunctorIso F G)
    (hF : IsRelativeLeftKanExtendedFrom U δ F) : IsRelativeLeftKanExtendedFrom U δ G := by
  intro c
  exact kanIsRelativeColimitCone_of_functorIso U (hF c)
    (FunctorIso.precomp e (kanLeftCanonicalCoconeMap δ c))

end SerrePositivity.InfinityCategories.F1B
