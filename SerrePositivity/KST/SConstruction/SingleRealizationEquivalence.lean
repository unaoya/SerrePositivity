module
public import SerrePositivity.KST.SConstruction.StableModelEquivalences
public import SerrePositivity.KST.SConstruction.ObjectSTrivialFibration
public import SerrePositivity.KST.SConstruction.SingleRealizationAdditivity

/-! # 単回実現による完全な同値の保存
概要：完全な逆データを持つ同値は object S と単回 core S• 実現の局所化同型を誘導する。
方針：元の関手同型を object S の実ホモトピーに移し、自然な object/core 比較で移送する。
規約：Kan 性を実現自体に仮定しない。使われ方：全正有限反復への帰納の基底。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel

/-- 完全な逆データを持つ同値の object S の像は局所化同型。 -/
lemma objectS_map_localized_isIso_of_equivalence {X Y : StableModel.{u}}
    (e : StableModelEquivalence X Y) :
    IsIso (AnodyneHomotopy.anodyneQ.map (objectSConstructionFunctor.map e.hom)) := by
  obtain ⟨s, ⟨H₀⟩, ⟨H₁⟩⟩ := objectS_map_isSimplicialHomotopyEquivalence_of_inverse
    e.hom e.inv e.homInvIso e.invHomIso
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have hQ := Localization.inverts Q SSet.anodyneExtensions
  exact ⟨⟨Q.map s,
    (Q.map_comp _ _).symm.trans ((AnodyneHomotopy.map_homotopy_eq Q hQ H₀).trans (Q.map_id _)),
    (Q.map_comp _ _).symm.trans ((AnodyneHomotopy.map_homotopy_eq Q hQ H₁).trans (Q.map_id _))⟩⟩

/-- 完全な逆データを持つ同値の単回 core S• 実現の像は局所化同型。 -/
lemma coreSRealization_map_localized_isIso_of_equivalence {X Y : StableModel.{u}}
    (e : StableModelEquivalence X Y) :
    IsIso (AnodyneHomotopy.anodyneQ.map (coreSRealizationFunctor.map e.hom)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hObject := objectS_map_localized_isIso_of_equivalence e
  have hX := objectToCoreSRealization_localized_isIso X.carrier
  have hY := objectToCoreSRealization_localized_isIso Y.carrier
  have he := congrArg Q.map (objectCoreRealizationComparison.naturality e.hom)
  change Q.map (objectSConstructionFunctor.map e.hom ≫ objectToCoreSRealization Y.carrier) =
    Q.map (objectToCoreSRealization X.carrier ≫ coreSRealizationFunctor.map e.hom) at he
  rw [Q.map_comp, Q.map_comp] at he
  have hi : IsIso (Q.map (objectToCoreSRealization X.carrier) ≫
      Q.map (coreSRealizationFunctor.map e.hom)) := he ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp hi

/-- 一回の既存の多重実現も完全な逆データを持つ同値を局所化同型に送る。 -/
lemma multiRealization_map_one_localized_isIso_of_equivalence {X Y : StableModel.{u}}
    (e : StableModelEquivalence X Y) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor 1).map e.hom)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := coreSRealization_map_localized_isIso_of_equivalence e
  have he := congrArg Q.map (coreSingleRealizationIso_naturality e.hom)
  rw [Q.map_comp, Q.map_comp] at he
  have hi : IsIso (Q.map (coreSingleRealizationIso X).hom ≫
      Q.map ((multiRealizationFunctor 1).map e.hom)) := he ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp hi

end SerrePositivity.KST.SConstruction
