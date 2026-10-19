module
public import SerrePositivity.KST.SConstruction.FamilyHomotopyChains
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneIntervalEndpoints

/-! # 元の全区間の射影を保持する補正有限列の実持ち上げ
概要：元の区間とその有限列を Kan fibration に沿って持ち上げ、全区間の射影を保持する。
方針：元の円柱の始点包含が anodyne であることを使い、同じ順番の各区間を持ち上げる。
規約：適合ホモトピーを成分の等式へ忘れず、元の全時刻の射影を保持する。
使われ方：全精密化族を延長する前に、一点上の境界補正列を実構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の全パラメータの区間を、始点と全時刻の射影を保持して持ち上げる。 -/
lemma exists_fibration_family_transport {U E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (f : U ⟶ E) {a : U ⟶ B} (H : SSet.Homotopy (f ≫ p) a) :
    ∃ g : U ⟶ E, g ≫ p = a ∧ ∃ V : SSet.Homotopy f g, V.h ≫ p = H.h := by
  have hp : SSet.modelCategoryQuillen.J.rlp p :=
    (SSet.modelCategoryQuillen.fibration_iff p).mp inferInstance
  have : HasLiftingProperty (SSet.ι₀ (X := U)) p :=
    SerrePositivity.SimplicialModel.AnodyneHomotopy.endpoint_zero_anodyne U p hp
  let sq : CommSq f SSet.ι₀ p H.h := ⟨H.h₀.symm⟩
  let g := SSet.ι₁ ≫ sq.lift
  let V : SSet.Homotopy f g :=
    { h := sq.lift
      h₀ := sq.fac_left
      h₁ := rfl
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  refine ⟨g, ?_, V, sq.fac_right⟩
  change (SSet.ι₁ ≫ sq.lift) ≫ p = a
  rw [Category.assoc, sq.fac_right, H.h₁]

/-- 元の補正有限列の全区間を同じ順序で射影する、実有限列の持ち上げ。 -/
lemma exists_familyHomotopyChain_lift_with_trace {U E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] {b a : U ⟶ B} (c : FamilyHomotopyChain b a)
    (f : U ⟶ E) (hf : f ≫ p = b) :
    ∃ g : U ⟶ E, g ≫ p = a ∧ ∃ d : FamilyHomotopyChain f g,
      (familyHomotopyChainTrace d).map (· ≫ p) = familyHomotopyChainTrace c := by
  induction c generalizing f with
  | nil b => exact ⟨f, hf, .nil f, rfl⟩
  | @cons b a k H tail ih =>
      cases hf
      obtain ⟨g, hg, V, hV⟩ := exists_fibration_family_transport p f H
      obtain ⟨g', hg', d, hd⟩ := ih g hg
      refine ⟨g', hg', .cons V d, ?_⟩
      change (V.h ≫ p) :: (familyHomotopyChainTrace d).map (· ≫ p) =
        H.h :: familyHomotopyChainTrace tail
      rw [hV, hd]

/-- 元の全区間を射影する補正有限列を、選んだ終点と共に実データとして保存する。 -/
def familyHomotopyChainLiftData {U E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] {b a : U ⟶ B} (c : FamilyHomotopyChain b a)
    (f : U ⟶ E) (hf : f ≫ p = b) :
    Σ g : U ⟶ E, {d : FamilyHomotopyChain f g // g ≫ p = a ∧
      (familyHomotopyChainTrace d).map (· ≫ p) = familyHomotopyChainTrace c} := by
  let hex := exists_familyHomotopyChain_lift_with_trace p c f hf
  exact ⟨hex.choose, ⟨hex.choose_spec.2.choose, hex.choose_spec.1, hex.choose_spec.2.choose_spec⟩⟩

end SerrePositivity.KST.SConstruction
