module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofRelativeFiberZero

/-! # 共通 fiber 還元と元の相対問題を結ぶホモトピー

概要：二つの prism から、固定 fiber 内の相対問題を元の境界・全体へ結ぶ実ホモトピーを得る。
方針：時間因子を入れ替え、端点・全面の比較と全底を元の prism の式で検証する。
規約：境界は全時刻で厳密に一致する。使われ方：実屋根比較の相対充填判定。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {A K E Q B : SSet.{u}} {i : A ⟶ K} {p : E ⟶ B} {q : Q ⟶ B}
variable {F : E ⟶ Q} {a : A ⟶ E} {g : K ⟶ Q} {β : (Δ[1] : SSet.{u}) ⊗ K ⟶ B}
namespace RoofRelativeFiberPrism
variable (T : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofRelativeFiberPrism i p q F a g β)
variable (b : B _⦋0⦌) (hzero : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ β = SSet.const b)

/-- 共通 fiber 上の元屋根境界から元の境界への実輸送。 -/
def sourceHomotopy : SSet.Homotopy (T.sourceFiber b hzero ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) a where
  h := (β_ A (Δ[1] : SSet.{u})).hom ≫ T.source
  h₀ := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ T.source = _
    exact (T.sourceFiber_ι b hzero).symm
  h₁ := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ T.source = a
    exact T.source_end
  rel := by
    ext n s
    exact False.elim s.1.property

/-- 共通 fiber 上の商屋根全体から元の全体への実輸送。 -/
def targetHomotopy : SSet.Homotopy (T.targetFiber b hzero ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b) g where
  h := (β_ K (Δ[1] : SSet.{u})).hom ≫ T.target
  h₀ := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ T.target = _
    exact (T.targetFiber_ι b hzero).symm
  h₁ := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ T.target = g
    exact T.target_end
  rel := by
    ext n s
    exact False.elim s.1.property

/-- 境界の二輸送は比較後に全時刻で厳密に一致する。 -/
lemma homotopy_boundary : (i ▷ (Δ[1] : SSet.{u})) ≫ (T.targetHomotopy b hzero).h =
    (T.sourceHomotopy b hzero).h ≫ F := by
  change (i ▷ Δ[1]) ≫ ((β_ K Δ[1]).hom ≫ T.target) =
    ((β_ A Δ[1]).hom ≫ T.source) ≫ F
  rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc,
    T.boundary, Category.assoc]

/-- 元屋根境界の全輸送は指定底 prism の同じ制限を被覆する。 -/
lemma sourceHomotopy_over : (T.sourceHomotopy b hzero).h ≫ p =
    (β_ A (Δ[1] : SSet.{u})).hom ≫ (Δ[1] ◁ i) ≫ β := by
  change ((β_ A Δ[1]).hom ≫ T.source) ≫ p = _
  rw [Category.assoc, T.source_over]

/-- 商屋根全体の全輸送は指定底 prism を被覆する。 -/
lemma targetHomotopy_over : (T.targetHomotopy b hzero).h ≫ q =
    (β_ K (Δ[1] : SSet.{u})).hom ≫ β := by
  change ((β_ K Δ[1]).hom ≫ T.target) ≫ q = _
  rw [Category.assoc, T.target_over]

end RoofRelativeFiberPrism
end SerrePositivity.InfinityCategories.Project.DerivedCategories
