module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationEndpointExtension
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-! # 指定した境界と適合円柱を保持する族の厳密化
概要：点つき写像族の源への制限を、境界を固定したまま指定した族へ厳密に一致させる。
方針：写像空間の制限の Kan fibration に、元の適合ホモトピーを相対的に持ち上げる。
規約：パラメータは任意。境界上でのホモトピーの定数性を明示し、全ホモトピーを保持する。
使われ方：元の K の列の構造可換式を、指定境界を保つパラメータ族で厳密化する帰納段。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open Spectra
open SerrePositivity.InfinityCategories
open SSet.modelCategoryQuillen
open scoped Simplicial

/-- Kan fibration に沿い、境界を固定して指定したホモトピーをそのまま持ち上げる。 -/
lemma exists_relative_fibration_family_transport {E B T U : SSet.{u}}
    (p : E ⟶ B) [Fibration p] (j : T ⟶ U) [Mono j]
    (f : U ⟶ E) {a : U ⟶ B} (H : SSet.Homotopy (f ≫ p) a)
    (hrel : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst T (Δ[1] : SSet.{u}) ≫ j ≫ f ≫ p) :
    ∃ g : U ⟶ E, g ≫ p = a ∧ j ≫ g = j ≫ f ∧
      ∃ V : SSet.Homotopy f g,
        (j ▷ (Δ[1] : SSet.{u})) ≫ V.h = fst T (Δ[1] : SSet.{u}) ≫ j ≫ f ∧
        V.h ≫ p = H.h := by
  have hp : SSet.modelCategoryQuillen.J.rlp p :=
    (SSet.modelCategoryQuillen.fibration_iff p).mp inferInstance
  have hc : (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (j ≫ f)).h ≫ p =
      (j ▷ (Δ[1] : SSet.{u})) ≫ H.h := hrel.symm
  obtain ⟨g, hg, V, hV, hbase⟩ :=
    SerrePositivity.SimplicialModel.KanFibrationEndpointExtension.exists_from_zero
      p hp j f (j ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (j ≫ f)) H.h H.h₀.symm hc
  refine ⟨g, ?_, hg, V, hV, hbase⟩
  calc
    g ≫ p = (SSet.ι₁ ≫ V.h) ≫ p := by rw [V.h₁]
    _ = SSet.ι₁ ≫ H.h := by rw [Category.assoc, hbase]
    _ = a := H.h₁

/-- 元の適合円柱を持ち上げ、指定したパラメータ境界を固定したまま族を厳密化する。 -/
lemma exists_relative_pointed_family_adjustment
    {A B Y : PointedSimplicialSet.{u}} [KanComplex Y.right]
    (i : A ⟶ B) [Mono i.right] {T U : SSet.{u}} (j : T ⟶ U) [Mono j]
    (f : U ⟶ (PointedObject.basedHom B Y).right)
    (a : U ⟶ (PointedObject.basedHom A Y).right)
    (H : SSet.Homotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Y) a)
    (hrel : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst T (Δ[1] : SSet.{u}) ≫ j ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Y) :
    ∃ g : U ⟶ (PointedObject.basedHom B Y).right,
      g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Y = a ∧ j ≫ g = j ≫ f ∧
      ∃ V : SSet.Homotopy f g,
        (j ▷ (Δ[1] : SSet.{u})) ≫ V.h = fst T (Δ[1] : SSet.{u}) ≫ j ≫ f ∧
        V.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Y = H.h := by
  let : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Y) := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration i Y
  exact exists_relative_fibration_family_transport (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Y) j f H hrel

end SerrePositivity.KST.SConstruction
