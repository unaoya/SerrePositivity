module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CospanFinitePathTransport
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ContinuousKanPathReflection

/-!
概要：輸送した指定有限 path の模型から、共通の値の Kan 置換内の実際の path を読む。
方針：元の有限 path の射を輸送先へ写し、両端の厳密な式を単位の自然性で移す。
規約：path の全円柱を新たに選び直さない。
使われ方：元の指定 path の比較円柱を保持する標的側の有限検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K M E D H B : SSet.{u}} (p : H ⟶ B) (f : E ⟶ H) (g : D ⟶ H) (b : B _⦋0⦌)
  (s : K ⟶ vertexFiber (f ≫ p) b) (t : K ⟶ vertexFiber (g ≫ p) b)
  (m : K ⨿ K ⟶ M) (z : K ⊗ (Δ[1] : SSet.{u}) ⟶ continuousKanReplacement.obj M)
  (w : M ⟶ vertexFiber p b)
  (hz : cylinderBoundaryInclusion K ≫ z = m ≫ continuousKanReplacementUnit.app M)
  (hw : m ≫ w = coprod.desc (s ≫ vertexFiberMap (f ≫ p) p f rfl b)
    (t ≫ vertexFiberMap (g ≫ p) p g rfl b))

/-- 概要：輸送した有限 path の射そのものが共通の標的値の Kan path を与える。
方針：両端の境界式を輸送先への関手と単位の自然性で写す。
規約：h は z の後の w の Kan 置換そのもの。使われ方：指定有限 path の全座標の追跡。 -/
def cospanTransportedKanPath :
    SSet.Homotopy ((s ≫ vertexFiberMap (f ≫ p) p f rfl b) ≫
      continuousKanReplacementUnit.app (vertexFiber p b))
      ((t ≫ vertexFiberMap (g ≫ p) p g rfl b) ≫
        continuousKanReplacementUnit.app (vertexFiber p b)) := by
  have hh : cylinderBoundaryInclusion K ≫ (z ≫ continuousKanReplacement.map w) =
      coprod.desc ((s ≫ vertexFiberMap (f ≫ p) p f rfl b) ≫
        continuousKanReplacementUnit.app (vertexFiber p b))
        ((t ≫ vertexFiberMap (g ≫ p) p g rfl b) ≫
          continuousKanReplacementUnit.app (vertexFiber p b)) := by
    rw [← Category.assoc, hz, Category.assoc, ← continuousKanReplacementUnit.naturality,
      CategoryTheory.Functor.id_map, ← Category.assoc, hw, coprod.desc_comp]
  refine { h := z ≫ continuousKanReplacement.map w, h₀ := ?_, h₁ := ?_, rel := ?_ }
  · change SSet.ι₀ ≫ (z ≫ continuousKanReplacement.map w) =
      (s ≫ vertexFiberMap (f ≫ p) p f rfl b) ≫ continuousKanReplacementUnit.app (vertexFiber p b)
    have h := congrArg (fun r ↦ (coprod.inl : K ⟶ K ⨿ K) ≫ r) hh
    simpa only [cylinderBoundaryInclusion, ← Category.assoc, coprod.inl_desc] using h
  · change SSet.ι₁ ≫ (z ≫ continuousKanReplacement.map w) =
      (t ≫ vertexFiberMap (g ≫ p) p g rfl b) ≫ continuousKanReplacementUnit.app (vertexFiber p b)
    have h := congrArg (fun r ↦ (coprod.inr : K ⟶ K ⨿ K) ≫ r) hh
    simpa only [cylinderBoundaryInclusion, ← Category.assoc, coprod.inr_desc] using h
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：読んだ path の全円柱は元の有限模型の輸送先への像そのもの。
方針：構成の定義。規約：選び直さない。使われ方：元の指定 path への比較の合成。 -/
lemma cospanTransportedKanPath_h :
    (cospanTransportedKanPath p f g b s t m z w hz hw).h = z ≫ continuousKanReplacement.map w := rfl

include m hz hw in
/-- 概要：輸送した指定 path を元の共通値へ端点固定で戻せる。
方針：指定全円柱 z の像を相対 path 反映へ渡す。
規約：比較の終端は z の像そのもの。使われ方：元の値の path 引き戻しへの接続。 -/
lemma cospanTransportedKanPath_reflection [KanComplex (vertexFiber p b)] :
    ∃ L : SSet.Homotopy (s ≫ vertexFiberMap (f ≫ p) p f rfl b)
      (t ≫ vertexFiberMap (g ≫ p) p g rfl b),
      ∃ G : SSet.Homotopy (L.h ≫ continuousKanReplacementUnit.app (vertexFiber p b))
        (z ≫ continuousKanReplacement.map w),
        (cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫ G.h =
          fst (K ⨿ K) (Δ[1] : SSet.{u}) ≫
            coprod.desc (s ≫ vertexFiberMap (f ≫ p) p f rfl b)
              (t ≫ vertexFiberMap (g ≫ p) p g rfl b) ≫
                continuousKanReplacementUnit.app (vertexFiber p b) :=
  continuousKanReplacement_path_reflection _ _
    (cospanTransportedKanPath p f g b s t m z w hz hw)

end SerrePositivity.InfinityCategories.F2
