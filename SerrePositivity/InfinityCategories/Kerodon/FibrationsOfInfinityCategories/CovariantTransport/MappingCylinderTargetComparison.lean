module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinder
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.MappingCylinderOverMono
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionPushoutGluing

/-!
概要：写像円柱の終域を同値な単体集合へ変更する比較。
方針：prism 部分を固定し、終域の射を押し出しで貼る。
規約：比較射に単射性は要求せず、貼り合わせる終点包含の単射性を使う。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、構造射の単射性の仮定の除去。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：写像円柱の終域側の比較が誘導する射。
方針：prism の恒等射と終域の射を pushout の普遍性で貼る。
規約：h は構造射の合成の厳密な等式。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、単射の因子分解による還元。 -/
noncomputable def mappingCylinderTargetMap {X Y Z : SSet.{u}}
    (f : X ⟶ Y) (g : X ⟶ Z) (q : Z ⟶ Y) (h : g ≫ q = f) :
    pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X) g ⟶ pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X) f :=
  pushout.desc (pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X) f) (q ≫ pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X) f)
    (by rw [← Category.assoc, h, pushout.condition])

/-- 概要：終域の比較が前合成同値なら誘導された写像円柱の比較も前合成同値。
方針：終点包含を共通の単射として pushout の三対象での同値を貼り合わせる。
規約：f と g の単射性や quasicategory 性は不要。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、終域の trivial Kan fibration による還元。 -/
lemma mappingCylinderTargetMap_isPrecompositionEquivalence {X Y Z : SSet.{u}}
    (f : X ⟶ Y) (g : X ⟶ Z) (q : Z ⟶ Y) (h : g ≫ q = f)
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (mappingCylinderTargetMap f g q h) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_pushout_gluing
    (IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X) g)
    (IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X) f)
    (𝟙 X) (𝟙 ((Δ[1] : SSet.{u}) ⊗ X)) q (mappingCylinderTargetMap f g q h)
  · simp
  · simpa only [Category.id_comp] using h
  · simp only [mappingCylinderTargetMap, pushout.inl_desc, Category.id_comp]
  · exact pushout.inr_desc _ _ _
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_id _
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_id _
  · exact hq

/-- 概要：終域の比較による円柱の射は与えた prism と終域の射の貼り合わせを保つ。
方針：pushout の二つの包含の後で計算する。
規約：w と v は各円柱での端点の整合条件。
使われ方：Kerodon Theorem 5.2.4.1（Tag 024N）、単射の円柱上の比較を元の円柱へ戻す。 -/
lemma mappingCylinderTargetMap_desc {X Y Z E : SSet.{u}}
    (f : X ⟶ Y) (g : X ⟶ Z) (q : Z ⟶ Y) (h : g ≫ q = f)
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (k : Y ⟶ E)
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X ≫ H = f ≫ k)
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X ≫ H = g ≫ (q ≫ k)) :
    mappingCylinderTargetMap f g q h ≫ pushout.desc H k w = pushout.desc H (q ≫ k) v := by
  apply pushout.hom_ext
  · simp only [mappingCylinderTargetMap, ← Category.assoc, pushout.inl_desc]
  · rw [← Category.assoc, mappingCylinderTargetMap, pushout.inr_desc,
      Category.assoc, pushout.inr_desc, pushout.inr_desc]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
