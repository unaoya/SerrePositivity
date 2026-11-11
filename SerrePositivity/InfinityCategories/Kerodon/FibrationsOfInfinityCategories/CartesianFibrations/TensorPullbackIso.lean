module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessTotalIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TensorFiber

/-!
概要：積のパラメーター制限は実際の底変換の引き戻しと厳密に同型。
方針：引き戻しの二成分から元の全空間成分と新しいパラメーターを取る。
規約：射影やパラメーターの充填性は不要。
使われ方：積の表現空間の制限を実際の境界制限へ同定する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：パラメーターの底変換で得る積の全空間は実際の引き戻し全空間と同型。
方針：元の全空間成分と新しいパラメーターの二成分で逆射を構成する。
規約：任意の射 p と i に対する厳密な同型。
使われ方：表現空間の実際の底変換への制限の比較。 -/
def transportTensorPullbackIso {E B K L : SSet.{u}} (p : E ⟶ B) (i : L ⟶ K) :
    E ⊗ L ≅ pullback (p ▷ K) (B ◁ i) := by
  let P := pullback (p ▷ K) (B ◁ i)
  let p₀ : P ⟶ E ⊗ K := pullback.fst _ _
  let p₁ : P ⟶ B ⊗ L := pullback.snd _ _
  let H : E ⊗ L ⟶ P := pullback.lift (E ◁ i) (p ▷ L) (whisker_exchange p i)
  let G : P ⟶ E ⊗ L := lift (p₀ ≫ fst E K) (p₁ ≫ snd B L)
  have hH₀ : H ≫ p₀ = E ◁ i := pullback.lift_fst _ _ _
  have hH₁ : H ≫ p₁ = p ▷ L := pullback.lift_snd _ _ _
  have hG₀ : G ≫ fst E L = p₀ ≫ fst E K := lift_fst _ _
  have hG₁ : G ≫ snd E L = p₁ ≫ snd B L := lift_snd _ _
  have hc₀ : p₀ ≫ fst E K ≫ p = p₁ ≫ fst B L := by
    have h := congrArg (fun f ↦ f ≫ fst B K)
      (pullback.condition (f := p ▷ K) (g := B ◁ i))
    simpa only [Category.assoc, whiskerRight_fst, whiskerLeft_fst] using h
  have hc₁ : p₀ ≫ snd E K = p₁ ≫ snd B L ≫ i := by
    have h := congrArg (fun f ↦ f ≫ snd B K)
      (pullback.condition (f := p ▷ K) (g := B ◁ i))
    simpa only [Category.assoc, whiskerRight_snd, whiskerLeft_snd] using h
  have hGpre : G ≫ (E ◁ i) = p₀ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, hG₀]
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, hG₁, Category.assoc]
      exact hc₁.symm
  have hGbase : G ≫ (p ▷ L) = p₁ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerRight_fst, ← Category.assoc, hG₀, Category.assoc]
      exact hc₀
    · rw [Category.assoc, whiskerRight_snd, hG₁]
  refine { hom := H, inv := G, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, hG₀, ← Category.assoc, hH₀, whiskerLeft_fst, Category.id_comp]
    · rw [Category.assoc, hG₁, ← Category.assoc, hH₁, whiskerRight_snd, Category.id_comp]
  · apply pullback.hom_ext
    · change (G ≫ H) ≫ p₀ = (𝟙 P) ≫ p₀
      rw [Category.assoc, hH₀, hGpre, Category.id_comp]
    · change (G ≫ H) ≫ p₁ = (𝟙 P) ≫ p₁
      rw [Category.assoc, hH₁, hGbase, Category.id_comp]

/-- 概要：積の引き戻し同型は元の全空間への射を保持する。
方針：引き戻しへの lift の第一射影。
規約：厳密な射の一致。
使われ方：pointed space 側の前合成の同定。 -/
lemma transportTensorPullbackIso_hom_fst {E B K L : SSet.{u}} (p : E ⟶ B) (i : L ⟶ K) :
    (transportTensorPullbackIso p i).hom ≫ pullback.fst (p ▷ K) (B ◁ i) = E ◁ i :=
  pullback.lift_fst _ _ _

/-- 概要：積の引き戻し同型は新しい底への射影を保持する。
方針：引き戻しへの lift の第二射影。
規約：厳密な底上の同型。
使われ方：表現空間の全空間同型による比較。 -/
lemma transportTensorPullbackIso_hom_snd {E B K L : SSet.{u}} (p : E ⟶ B) (i : L ⟶ K) :
    (transportTensorPullbackIso p i).hom ≫ pullback.snd (p ▷ K) (B ◁ i) = p ▷ L :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
