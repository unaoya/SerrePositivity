module
public import SerrePositivity.DifferentialGraded.Resolution.InitialComparison

/-!
概要：同じ初期 cycle 被覆の比較関手の厳密恒等則・合成則。
方針：自由 dg 圏の同じ生成辺の普遍性と cycle 被覆の厳密関手性を使う。
規約：通常 dg 射の則であり、全 native Hom への作用はまだ主張しない。
使われ方：D-8 e の固定 cell 分解作用の初期段。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.DGCategoryCycleCover
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma map_identity : map A D D (DGFunctor.id D) = DGFunctor.id (Source A D) := by
  apply (FreeDGCategory.universalEquiv A D (Source A D) (edges A D)).injective
  change (⟨id, fun x y => FreeDGCategory.edgeInclusion A D (edges A D) x y ≫
    (map A D D (DGFunctor.id D)).map x y⟩ :
      FreeDGCategory.GeneratorMap A D (Source A D) (edges A D)) =
    ⟨id, fun x y => FreeDGCategory.edgeInclusion A D (edges A D) x y ≫ 𝟙 _⟩
  congr 1
  funext x y
  rw [edge_map]
  change complexCycleCoverMap A (𝟙 _) ≫ _ = _
  rw [complexCycleCoverMap_id, Category.id_comp, Category.comp_id]
  rfl

variable (E : Type w) [DGCategory A E] [Small.{u} E]
  (B : Type z) [DGCategory A B] [Small.{u} B]

lemma map_composition (F : DGFunctor A D E) (G : DGFunctor A E B) :
    map A D B (F.comp G) = (map A D E F).comp (map A E B G) := by
  apply (FreeDGCategory.universalEquiv A D (Source A B) (edges A D)).injective
  change (⟨G.obj ∘ F.obj, fun x y => FreeDGCategory.edgeInclusion A D (edges A D) x y ≫
    (map A D B (F.comp G)).map x y⟩ :
      FreeDGCategory.GeneratorMap A D (Source A B) (edges A D)) =
    ⟨G.obj ∘ F.obj, fun x y => FreeDGCategory.edgeInclusion A D (edges A D) x y ≫
      ((map A D E F).map x y ≫ (map A E B G).map (F.obj x) (F.obj y))⟩
  congr 1
  funext x y
  rw [edge_map, ← Category.assoc, edge_map, Category.assoc, edge_map]
  change complexCycleCoverMap A (F.map x y ≫ G.map (F.obj x) (F.obj y)) ≫ _ = _
  rw [complexCycleCoverMap_comp, Category.assoc]
  rfl

end SerrePositivity.DifferentialGraded.DGCategoryCycleCover
