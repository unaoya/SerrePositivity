module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-!
概要：底を固定する実際のホモトピーを、指定部分で評価して一点の fiber 内のホモトピーへ移す。
方針：raw な円柱の射を制限し、底が定値となる式を使って fiber へ持ち上げる。
規約：辺の代表を選び直さず、元の円柱への射影を厳密に保持する。
使われ方：三角形 prism の長辺の比較を、二段階輸送と標準長辺輸送の実際の比較にする。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 底を固定するホモトピーの指定した部分を、一点の fiber 内の実際のホモトピーにする。 -/
def constantBaseEndpointHomotopy {D A E B : SSet.{u}}
    (p : E ⟶ B) (β : D ⟶ B) {W W' : D ⟶ E} (H : SSet.Homotopy W W')
    (hH : H.h ≫ p = fst D (Δ[1] : SSet.{u}) ≫ β)
    (j : A ⟶ D) (b : B _⦋0⦌) (hj : j ≫ β = SSet.const b)
    (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)
    (hf : j ≫ W = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (hg : j ≫ W' = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) :
    SSet.Homotopy f g := by
  let K : SSet.Homotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) :=
    { h := (j ▷ (Δ[1] : SSet.{u})) ≫ H.h
      h₀ := by rw [SSet.ι₀_comp_assoc, H.h₀, hf]; rfl
      h₁ := by rw [SSet.ι₁_comp_assoc, H.h₁, hg]; rfl
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro s
        exact False.elim s.1.property }
  have hK : K.h ≫ p = SSet.const b := by
    dsimp only [K]
    rw [Category.assoc, hH, ← Category.assoc, whiskerRight_fst,
      Category.assoc, hj, SSet.comp_const]
  exact
    { h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b K.h hK
      h₀ := by
        apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
        rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, K.h₀]; rfl
      h₁ := by
        apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
        rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, K.h₁]; rfl
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro s
        exact False.elim s.1.property }

/-- fiber 内の比較の円柱は、包含後に元の指定した円柱の制限そのものになる。 -/
lemma constantBaseEndpointHomotopy_projection {D A E B : SSet.{u}}
    (p : E ⟶ B) (β : D ⟶ B) {W W' : D ⟶ E} (H : SSet.Homotopy W W')
    (hH : H.h ≫ p = fst D (Δ[1] : SSet.{u}) ≫ β)
    (j : A ⟶ D) (b : B _⦋0⦌) (hj : j ≫ β = SSet.const b)
    (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)
    (hf : j ≫ W = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (hg : j ≫ W' = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) :
    (constantBaseEndpointHomotopy p β H hH j b hj f g hf hg).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b =
      (j ▷ (Δ[1] : SSet.{u})) ≫ H.h :=
by
  dsimp only [constantBaseEndpointHomotopy]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
