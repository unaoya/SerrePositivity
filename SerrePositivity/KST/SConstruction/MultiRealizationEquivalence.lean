module
public import SerrePositivity.KST.SConstruction.SingleRealizationEquivalence
public import SerrePositivity.KST.SConstruction.InnerZeroBoundaryNaturality
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence

/-! # 正の反復実現による完全な同値の保存
概要：完全な逆データを持つ同値は全正有限反復の core S• 実現の局所化同型を誘導する。
方針：各 S_n の完全な逆データを対角へ移し、自然な反復座標同型で帰納する。
規約：実現の Kan 性は仮定しない。使われ方：支持部分圏の同値と Segal 射の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel

/-- 前段の同値保存から次の反復実現の同値保存が従う。 -/
lemma multiRealization_map_step_localized_isIso_of_equivalence (r : ℕ)
    (hr : ∀ {X Y : StableModel.{u}} (e : StableModelEquivalence X Y),
      IsIso (AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor r).map e.hom)))
    {X Y : StableModel.{u}} (e : StableModelEquivalence X Y) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor (r + 1)).map e.hom)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hd : IsIso (Q.map (simplicialDiagonalFunctor.map
      (iteratedSRealizationDiagramMap r e.hom))) :=
    SerrePositivity.BisimplicialModel.localized_diagonal_map
      (iteratedSRealizationDiagramMap r e.hom) (fun n => hr (e.sConstruction n.unop.len))
  have hi : IsIso (Q.map (iteratedSRealizationMap r e.hom)) := hd
  have he := congrArg Q.map (iteratedSRealizationCoordinateIso_naturality r e.hom)
  rw [Q.map_comp, Q.map_comp] at he
  have hc : IsIso (Q.map (iteratedSRealizationCoordinateIso r X).hom ≫
      Q.map ((multiRealizationFunctor (r + 1)).map e.hom)) := he ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp hc

/-- 全正有限反復の実現は完全な逆データを持つ同値を局所化同型に送る。 -/
lemma multiRealization_map_localized_isIso_of_equivalence (r : ℕ)
    {X Y : StableModel.{u}} (e : StableModelEquivalence X Y) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor (r + 1)).map e.hom)) := by
  induction r generalizing X Y with
  | zero => exact multiRealization_map_one_localized_isIso_of_equivalence e
  | succ r ih =>
    exact multiRealization_map_step_localized_isIso_of_equivalence (r + 1) ih e

end SerrePositivity.KST.SConstruction
