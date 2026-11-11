module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FiberTransportFamilyNaturality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportFamilyPrismIdentity

/-!
概要：元の輸送族の恒等初期係数による前合成は、元の実 prism と実終点を変えない。
方針：元の係数前合成の定義とモノイダル恒等則を計算する。
規約：元の選択済み輸送族を保持。使われ方：恒等初期値の普遍比較の余分な因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B K L : SSet.{u}} {p : E ⟶ B} {a b : B _⦋0⦌}
  {f : K ⟶ vertexFiber p a} {γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B}
  (T : FiberTransportFamily (b := b) p f γ)

/-- 元の恒等初期係数で前合成した実 prism は、元の同じ実 prism。 -/
lemma fiberTransportFamily_precomposeSource_id_prism :
    (T.precomposeSource (𝟙 K)).prism = T.prism := by
  change (Δ[1] ◁ (𝟙 K ▷ L)) ≫ T.prism = T.prism
  rw [id_whiskerRight, whiskerLeft_id, Category.id_comp]

/-- 元の恒等初期係数で前合成した実終点は、元の同じ実終点。 -/
lemma fiberTransportFamily_precomposeSource_id_endpoint :
    (T.precomposeSource (𝟙 K)).endpoint = T.endpoint := by
  change (𝟙 K ▷ L) ≫ T.endpoint = T.endpoint
  rw [id_whiskerRight, Category.id_comp]

end SerrePositivity.InfinityCategories.F2
