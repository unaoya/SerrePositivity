module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
概要：定値射に沿う引き戻しを、その頂点の fiber と底の直積に同定する。
方針：第一射影を fiber に制限し、逆射を fiber の包含と第二射影で構成する。
規約：fibration 性・充填性は不要。底への射影を厳密に保持する。
使われ方：一般 coherent 図式の余極限性に使う定値 unstraightening の比較。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：定値射による引き戻しは fiber と底の直積に同型。
方針：引き戻しと fiber の普遍性で両方向を構成し、両射影で逆を確認する。
規約：第一因子は fiber、第二因子は元の底。使われ方：定値図式の全空間。 -/
def constantPullbackFiberIso {E B K : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    pullback p (SSet.const b : K ⟶ B) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⊗ K := by
  let c : K ⟶ B := SSet.const b
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b (pullback.fst p c) (by
    rw [pullback.condition, SSet.comp_const])
  let H := lift j (pullback.snd p c)
  let V : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⊗ K ⟶ pullback p c :=
    pullback.lift (fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) K) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.comp_const])
  have hHf : H ≫ fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) K = j := lift_fst _ _
  have hHs : H ≫ snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) K = pullback.snd p c := lift_snd _ _
  have hVf : V ≫ pullback.fst p c = fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b :=
    pullback.lift_fst _ _ _
  have hVs : V ≫ pullback.snd p c = snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) K := pullback.lift_snd _ _ _
  refine ⟨H, V, ?_, ?_⟩
  · apply pullback.hom_ext
    · change (H ≫ V) ≫ pullback.fst p c = (𝟙 _) ≫ pullback.fst p c
      rw [Category.assoc, hVf, ← Category.assoc, hHf, Category.id_comp]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
    · change (H ≫ V) ≫ pullback.snd p c = (𝟙 _) ≫ pullback.snd p c
      rw [Category.assoc, hVs, hHs, Category.id_comp]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, hHf, Category.id_comp]
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
      change (V ≫ j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b = fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, hVf]
    · rw [Category.assoc, hHs, hVs, Category.id_comp]

/-- 概要：定値引き戻しの比較は元の底への第二射影を保持する。
方針：直積への持ち上げの第二成分を取る。
規約：元の射影との厳密な一致。使われ方：底上の相対関手空間の比較。 -/
lemma constantPullbackFiberIso_snd {E B K : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (constantPullbackFiberIso (K := K) p b).hom ≫ snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) K =
      pullback.snd p (SSet.const b : K ⟶ B) := by
  dsimp only [constantPullbackFiberIso]
  exact lift_snd _ _

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
