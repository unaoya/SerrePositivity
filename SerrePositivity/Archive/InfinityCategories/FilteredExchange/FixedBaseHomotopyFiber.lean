module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeVertexIsoHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorFiberHom

/-!
概要：底を全時刻で固定した元の円柱を同じ fiber 間の円柱へ制限する。
方針：始域 fiber で前合成し、全円柱の底の式で標的 fiber へ持ち上げる。
規約：全時刻の元の円柱を保持。使われ方：模型の全 path と指定相対比較の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A E B : SSet.{u}} (a : A ⟶ B) (p : E ⟶ B) {f g : A ⟶ E}
  (hf : f ≫ p = a) (hg : g ≫ p = a) (H : SSet.Homotopy f g)
  (hH : H.h ≫ p = fst A (Δ[1] : SSet.{u}) ≫ a) (b : B _⦋0⦌)

/-- 元の底固定円柱を同じ fiber 間のホモトピーへ制限する。 -/
def fixedBaseHomotopyFiber :
    SSet.Homotopy (vertexFiberMap a p f hf b) (vertexFiberMap a p g hg b) where
  h := vertexFiberLift p b ((vertexFiberι a b ▷ (Δ[1] : SSet.{u})) ≫ H.h) (by
    rw [Category.assoc, hH, ← Category.assoc, whiskerRight_fst, Category.assoc,
      vertexFiberι_comp, SSet.comp_const])
  h₀ := by
    apply vertexFiber_hom_ext p b
    rw [Category.assoc, vertexFiberLift_ι, SSet.ι₀_comp_assoc, H.h₀]
    exact (vertexFiberMap_ι a p f hf b).symm
  h₁ := by
    apply vertexFiber_hom_ext p b
    rw [Category.assoc, vertexFiberLift_ι, SSet.ι₁_comp_assoc, H.h₁]
    exact (vertexFiberMap_ι a p g hg b).symm
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- fiber 円柱を元の標的へ含めると、元の全時刻の円柱の同じ制限。 -/
lemma fixedBaseHomotopyFiber_h_ι :
    (fixedBaseHomotopyFiber a p hf hg H hH b).h ≫ vertexFiberι p b =
      (vertexFiberι a b ▷ (Δ[1] : SSet.{u})) ≫ H.h := rfl

end SerrePositivity.InfinityCategories.F2
