module

public import SerrePositivity.InfinityCategories.F1.MappingCylinderTargetComparison

/-!
概要：構造射の可換四角形から誘導される写像円柱の比較。
方針：係数の比較の prism と終域の比較を押し出しで貼る。
規約：因子の比較は単射である必要はない。
使われ方：Kerodon Theorem 5.2.4.1、因子を quasicategory へ置換した円柱の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：構造射の間の可換四角形が写像円柱に誘導する射。
方針：prism の係数を a で写し、終域を b で写して貼る。
規約：h は構造射の可換性。
使われ方：Kerodon Theorem 5.2.4.1、両因子の置換の比較。 -/
noncomputable def mappingCylinderMap {X Y X' Y' : SSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ f') :
    pushout (prismEndpoint 1 X) f ⟶ pushout (prismEndpoint 1 X') f' :=
  pushout.desc ((Δ[1] ◁ a) ≫ pushout.inl (prismEndpoint 1 X') f')
    (b ≫ pushout.inr (prismEndpoint 1 X') f') (by
      rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, pushout.condition,
        ← Category.assoc, ← h, Category.assoc])

/-- 概要：因子の比較がともに前合成同値なら写像円柱の比較も前合成同値。
方針：二つの押し出しの比較に、a とその prism および b の同値を使う。
規約：構造射や因子の比較の単射性は不要。
使われ方：Kerodon Theorem 5.2.4.1、置換前後の円柱の同値。 -/
lemma mappingCylinderMap_isPrecompositionEquivalence {X Y X' Y' : SSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ f')
    (ha : IsPrecompositionEquivalence a) (hb : IsPrecompositionEquivalence b) :
    IsPrecompositionEquivalence (mappingCylinderMap f f' a b h) := by
  apply isPrecompositionEquivalence_of_pushout_gluing
    (IsPushout.of_hasPushout (prismEndpoint 1 X) f)
    (IsPushout.of_hasPushout (prismEndpoint 1 X') f')
    a (Δ[1] ◁ a) b (mappingCylinderMap f f' a b h)
  · exact prismEndpoint_naturality 1 a
  · exact h
  · exact pushout.inl_desc _ _ _
  · exact pushout.inr_desc _ _ _
  · exact ha
  · exact ha.whiskerLeft Δ[1]
  · exact hb

/-- 概要：比較図式の延長を貼った円柱からの射は円柱の比較と可換。
方針：prism と終域の包含後で押し出しの式を計算する。
規約：hH と hg は延長された二射の制限の一致。
使われ方：Kerodon Theorem 5.2.4.1、置換先の同値判定から元の比較を回収する。 -/
lemma mappingCylinderMap_desc {X Y X' Y' E : SSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ f')
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ E) (g : Y ⟶ E)
    (H' : (Δ[1] : SSet.{u}) ⊗ X' ⟶ E) (g' : Y' ⟶ E)
    (w : prismEndpoint 1 X ≫ H = f ≫ g) (w' : prismEndpoint 1 X' ≫ H' = f' ≫ g')
    (hH : (Δ[1] ◁ a) ≫ H' = H) (hg : b ≫ g' = g) :
    mappingCylinderMap f f' a b h ≫ pushout.desc H' g' w' = pushout.desc H g w := by
  apply pushout.hom_ext
  · rw [← Category.assoc, mappingCylinderMap, pushout.inl_desc, Category.assoc,
      pushout.inl_desc, hH, pushout.inl_desc]
  · rw [← Category.assoc, mappingCylinderMap, pushout.inr_desc, Category.assoc,
      pushout.inr_desc, hg, pushout.inr_desc]

end SerrePositivity.InfinityCategories
