module
public import SerrePositivity.KST.SConstruction.RelativeFamilyRectification

/-! # 指定した元の境界円柱を保持する族の持ち上げ
概要：境界が定数でない場合も、指定した元の境界円柱と射影区間を同時に保持する。
方針：Kan fibration の指定端点・指定境界の区間延長をそのまま用いる。
規約：境界の円柱を定数に置き換えず、指定した実区間を回収する。
使われ方：元の K prism の指定境界の補正有限列を保つ厳密化の帰納段。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open Spectra SerrePositivity.InfinityCategories
open SSet.modelCategoryQuillen
open scoped Simplicial

/-- 全パラメータの元の区間を、指定した境界の実区間を厳密に保持して持ち上げる。 -/
lemma exists_prescribed_fibration_family_transport {E B T U : SSet.{u}}
    (p : E ⟶ B) [Fibration p] (j : T ⟶ U) [Mono j]
    (f : U ⟶ E) {a : U ⟶ B} (H : SSet.Homotopy (f ≫ p) a)
    {g : T ⟶ E} (V : SSet.Homotopy (j ≫ f) g)
    (hV : V.h ≫ p = (j ▷ (Δ[1] : SSet.{u})) ≫ H.h) :
    ∃ k : U ⟶ E, k ≫ p = a ∧ j ≫ k = g ∧ ∃ W : SSet.Homotopy f k,
      (j ▷ (Δ[1] : SSet.{u})) ≫ W.h = V.h ∧ W.h ≫ p = H.h := by
  have hp : SSet.modelCategoryQuillen.J.rlp p :=
    (SSet.modelCategoryQuillen.fibration_iff p).mp inferInstance
  obtain ⟨k, hk, W, hW, hbase⟩ :=
    SerrePositivity.SimplicialModel.KanFibrationEndpointExtension.exists_from_zero
      p hp j f g V H.h H.h₀.symm hV
  refine ⟨k, ?_, hk, W, hW, hbase⟩
  calc
    k ≫ p = (SSet.ι₁ ≫ W.h) ≫ p := by rw [W.h₁]
    _ = SSet.ι₁ ≫ H.h := by rw [Category.assoc, hbase]
    _ = a := H.h₁

/-- 源の単射の写像空間制限に沿い、元の全区間と指定境界区間を同時に持ち上げる。 -/
lemma exists_prescribed_pointed_family_adjustment
    {A B Y : PointedSimplicialSet.{u}} [KanComplex Y.right]
    (i : A ⟶ B) [Mono i.right] {T U : SSet.{u}} (j : T ⟶ U) [Mono j]
    (f : U ⟶ (PointedObject.basedHom B Y).right)
    {a : U ⟶ (PointedObject.basedHom A Y).right}
    (H : SSet.Homotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Y) a)
    {g : T ⟶ (PointedObject.basedHom B Y).right}
    (V : SSet.Homotopy (j ≫ f) g)
    (hV : V.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Y = (j ▷ (Δ[1] : SSet.{u})) ≫ H.h) :
    ∃ k : U ⟶ (PointedObject.basedHom B Y).right,
      k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Y = a ∧ j ≫ k = g ∧ ∃ W : SSet.Homotopy f k,
        (j ▷ (Δ[1] : SSet.{u})) ≫ W.h = V.h ∧ W.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Y = H.h := by
  let : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Y) := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration i Y
  exact exists_prescribed_fibration_family_transport _ j f H V hV

end SerrePositivity.KST.SConstruction
