module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointProductWitnessTensorIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessTotalIso

/-!
概要：積の第二射影の底変換を同じ第一因子との積へ厳密に同定する。
方針：引き戻しの第一成分の第一因子と第二射影を組にする。
規約：任意のパラメーターの射を扱う。
使われ方：実際の区間境界上の全空間の正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks

/-- 概要：積射影の底変換の全空間は元の第一因子と新しい底の積。
方針：引き戻しの普遍性と二つの直積射影で互いに逆の射を作る。
規約：射や単体集合の充填性は不要。
使われ方：区間境界の実際の全空間と端点族の比較。 -/
def productProjectionPullbackIso (E : SSet.{u}) {K L : SSet.{u}} (i : L ⟶ K) :
    E ⊗ L ≅ pullback (snd E K) i := by
  let P := pullback (snd E K) i
  let p₀ : P ⟶ E ⊗ K := pullback.fst _ _
  let p₁ : P ⟶ L := pullback.snd _ _
  let H : E ⊗ L ⟶ P := pullback.lift (E ◁ i) (snd E L) (whiskerLeft_snd E i)
  let G : P ⟶ E ⊗ L := lift (p₀ ≫ fst E K) p₁
  have hH₀ : H ≫ p₀ = E ◁ i := pullback.lift_fst _ _ _
  have hH₁ : H ≫ p₁ = snd E L := pullback.lift_snd _ _ _
  have hG₀ : G ≫ fst E L = p₀ ≫ fst E K := lift_fst _ _
  have hG₁ : G ≫ snd E L = p₁ := lift_snd _ _
  have hGH₀ : G ≫ (E ◁ i) = p₀ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, whiskerLeft_fst, hG₀]
    · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, hG₁]
      exact (pullback.condition (f := snd E K) (g := i)).symm
  refine { hom := H, inv := G, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, hG₀, ← Category.assoc, hH₀, whiskerLeft_fst, Category.id_comp]
    · rw [Category.assoc, hG₁, hH₁, Category.id_comp]
  · apply pullback.hom_ext
    · change (G ≫ H) ≫ p₀ = (𝟙 P) ≫ p₀
      rw [Category.assoc, hH₀, hGH₀, Category.id_comp]
    · change (G ≫ H) ≫ p₁ = (𝟙 P) ≫ p₁
      rw [Category.assoc, hH₁, hG₁, Category.id_comp]

/-- 概要：積射影の引き戻し同型は元の全空間への前合成を回収する。
方針：引き戻しへの lift の第一射影。
規約：厳密な射の一致。
使われ方：pointed space への写像の境界固定条件。 -/
lemma productProjectionPullbackIso_hom_fst (E : SSet.{u}) {K L : SSet.{u}} (i : L ⟶ K) :
    (productProjectionPullbackIso E i).hom ≫ pullback.fst (snd E K) i = E ◁ i :=
  pullback.lift_fst _ _ _

/-- 概要：積射影の引き戻し同型は新しい底への射影を保つ。
方針：引き戻しへの lift の第二射影。
規約：厳密な底上の同型。
使われ方：実際の境界制限の表現空間への同型の移送。 -/
lemma productProjectionPullbackIso_hom_snd (E : SSet.{u}) {K L : SSet.{u}} (i : L ⟶ K) :
    (productProjectionPullbackIso E i).hom ≫ pullback.snd (snd E K) i = snd E L :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks
