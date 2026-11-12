module
public import SerrePositivity.KST.SConstruction.FamilyHomotopyChains

/-! # 指定境界の全補正区間を保持する有限列の持ち上げ
概要：元の補正有限列を、指定した境界の補正有限列と射影 trace を同時に保持して持ち上げる。
方針：同じ順番の各区間を指定境界円柱付きで延長し、始点の表示だけを移して帰納する。
規約：境界の各区間は定数でなくてよく、元の実区間を全て厳密に回収する。
使われ方：元の K の指定 BF 境界を保持する族の厳密化の全段の補正。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open Spectra SerrePositivity.InfinityCategories
open SSet.modelCategoryQuillen
open scoped Simplicial

/-- 元の全区間と、指定した境界の全区間を同じ順序で保持する有限列の持ち上げ。 -/
lemma exists_prescribedFamilyChain_lift_with_traces {T U E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] (j : T ⟶ U) [Mono j]
    {b a : U ⟶ B} (c : FamilyHomotopyChain b a)
    (f : U ⟶ E) (hf : f ≫ p = b) {t : T ⟶ E}
    (d : FamilyHomotopyChain (j ≫ f) t)
    (htrace : (familyHomotopyChainTrace d).map (· ≫ p) =
      (familyHomotopyChainTrace c).map ((j ▷ (Δ[1] : SSet.{u})) ≫ ·)) :
    ∃ g : U ⟶ E, g ≫ p = a ∧ j ≫ g = t ∧ ∃ v : FamilyHomotopyChain f g,
      (familyHomotopyChainTrace v).map (· ≫ p) = familyHomotopyChainTrace c ∧
      (familyHomotopyChainTrace v).map ((j ▷ (Δ[1] : SSet.{u})) ≫ ·) =
        familyHomotopyChainTrace d := by
  induction c generalizing f t with
  | nil b =>
      cases d with
      | nil => exact ⟨f, hf, rfl, .nil f, rfl, rfl⟩
      | cons V tail =>
          simp only [familyHomotopyChainTrace, List.map_cons, List.map_nil] at htrace
          cases htrace
  | @cons b a k H tail ih =>
      cases hf
      cases d with
      | nil =>
          simp only [familyHomotopyChainTrace, List.map_cons, List.map_nil] at htrace
          cases htrace
      | @cons _ gT _ V dTail =>
          have hh := (List.cons.inj htrace).1
          have ht := (List.cons.inj htrace).2
          obtain ⟨g, hg, hjg, W, hW, hbase⟩ :=
            exists_prescribed_fibration_family_transport p j f H V hh
          let dTail' := familyHomotopyChainSourceTransport dTail hjg
          have ht' : (familyHomotopyChainTrace dTail').map (· ≫ p) =
              (familyHomotopyChainTrace tail).map ((j ▷ (Δ[1] : SSet.{u})) ≫ ·) := by
            rw [familyHomotopyChainSourceTransport_trace]
            exact ht
          obtain ⟨g', hg', hjg', vTail, hvbase, hvrel⟩ := ih g hg dTail' ht'
          refine ⟨g', hg', hjg', .cons W vTail, ?_, ?_⟩
          · change (W.h ≫ p) :: (familyHomotopyChainTrace vTail).map (· ≫ p) =
              H.h :: familyHomotopyChainTrace tail
            rw [hbase, hvbase]
          · change ((j ▷ (Δ[1] : SSet.{u})) ≫ W.h) ::
                (familyHomotopyChainTrace vTail).map ((j ▷ (Δ[1] : SSet.{u})) ≫ ·) =
              V.h :: familyHomotopyChainTrace dTail
            rw [hW, hvrel, familyHomotopyChainSourceTransport_trace]

/-- 元の全区間と指定境界区間を保持した、実際に選んだ持ち上げと補正有限列。 -/
def prescribedFamilyChainLiftData {T U E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] (j : T ⟶ U) [Mono j]
    {b a : U ⟶ B} (c : FamilyHomotopyChain b a)
    (f : U ⟶ E) (hf : f ≫ p = b) {t : T ⟶ E}
    (d : FamilyHomotopyChain (j ≫ f) t)
    (htrace : (familyHomotopyChainTrace d).map (· ≫ p) =
      (familyHomotopyChainTrace c).map ((j ▷ (Δ[1] : SSet.{u})) ≫ ·)) :
    Σ g : U ⟶ E, {v : FamilyHomotopyChain f g //
      g ≫ p = a ∧ j ≫ g = t ∧
      (familyHomotopyChainTrace v).map (· ≫ p) = familyHomotopyChainTrace c ∧
      (familyHomotopyChainTrace v).map ((j ▷ (Δ[1] : SSet.{u})) ≫ ·) =
        familyHomotopyChainTrace d} := by
  let hex := exists_prescribedFamilyChain_lift_with_traces p j c f hf d htrace
  exact ⟨hex.choose, ⟨hex.choose_spec.2.2.choose,
    hex.choose_spec.1, hex.choose_spec.2.1,
    hex.choose_spec.2.2.choose_spec.1, hex.choose_spec.2.2.choose_spec.2⟩⟩

/-- 単射の源の写像空間制限に沿い、元の全補正区間と指定境界の全区間を保持する。 -/
lemma exists_prescribed_pointedFamilyChain_lift_with_traces
    {A B Y : PointedSimplicialSet.{u}} [KanComplex Y.right]
    (i : A ⟶ B) [Mono i.right] {T U : SSet.{u}} (j : T ⟶ U) [Mono j]
    {a b : U ⟶ (PointedObject.basedHom A Y).right} (c : FamilyHomotopyChain b a)
    (f : U ⟶ (PointedObject.basedHom B Y).right) (hf : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Y = b)
    {t : T ⟶ (PointedObject.basedHom B Y).right} (d : FamilyHomotopyChain (j ≫ f) t)
    (htrace : (familyHomotopyChainTrace d).map (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Y) =
      (familyHomotopyChainTrace c).map ((j ▷ (Δ[1] : SSet.{u})) ≫ ·)) :
    ∃ g : U ⟶ (PointedObject.basedHom B Y).right,
      g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Y = a ∧ j ≫ g = t ∧ ∃ v : FamilyHomotopyChain f g,
        (familyHomotopyChainTrace v).map (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Y) =
          familyHomotopyChainTrace c ∧
        (familyHomotopyChainTrace v).map ((j ▷ (Δ[1] : SSet.{u})) ≫ ·) =
          familyHomotopyChainTrace d := by
  let : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Y) := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration i Y
  exact exists_prescribedFamilyChain_lift_with_traces _ j c f hf d htrace

end SerrePositivity.KST.SConstruction
