module

public import SerrePositivity.InfinityCategories.HomotopyLimits.NormalizedEdgeFamilyHomotopy

/-!
概要：元の全辺の族と native な前合成の比較を、終点固定の実際の円柱として保持する。
方針：終点評価上の切断比較をデータ化し、その同じ円柱を始点へ制限する。
規約：元の辺・全 Hom パラメータ・終点評価と raw な円柱の射影を保持する。
使われ方：指定四面体の中間 Hom 比較を native な共通脚の前合成へ接続する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {X T : SSet.{u}} [Quasicategory X] (e : (Δ[1] : SSet.{u}) ⟶ X)
  (y : X _⦋0⦌) (F : T ⟶ coconeMappingSpace e y)

/-- 元の辺の族と切断による族を比較する、終点評価固定の実際の円柱。 -/
structure CosliceEdgeFamilyCylinder where
  homotopy : SSet.Homotopy F
    ((F ≫ cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y) ≫ cosliceEdgeSectionFiber e y)
  target : homotopy.h ≫ cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y =
    fst T (Δ[1] : SSet.{u}) ≫ F ≫ cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y

/-- 元の族と同じ終点を全時刻で保つ、実際の比較データを構成する。 -/
def cosliceEdgeFamilyCylinder : CosliceEdgeFamilyCylinder e y F :=
  Classical.choice (by
    obtain ⟨H, hH⟩ := cosliceEdgeFamily_section_homotopy e y F
    exact ⟨⟨H, hH⟩⟩)

variable (a b : (Δ[0] : SSet.{u}) ⟶ X)
  (ha : stdSimplex.δ (1 : Fin 2) ≫ e = a) (hb : stdSimplex.δ (0 : Fin 2) ≫ e = b)

/-- 同じ終点固定円柱を始点へ射影した、正規化した実際の前合成との比較。 -/
def cosliceEdgeFamilyPrecompositionCylinder : SSet.Homotopy
    (F ≫ normalizedCoconeRestrictionFiber e (stdSimplex.δ (1 : Fin 2)) ha y)
    ((F ≫ normalizedCoconeRestrictionFiber e (stdSimplex.δ (0 : Fin 2)) hb y) ≫
      cosliceEdgeFiberPrecomposition e a b ha hb y) := by
  cases hb
  let H := functorHomotopyPostcomp (cosliceEdgeFamilyCylinder e y F).homotopy
    (normalizedCoconeRestrictionFiber e (stdSimplex.δ (1 : Fin 2)) ha y)
  exact
    { h := H.h
      h₀ := by
        change SSet.ι₀ ≫ H.h = F ≫ _
        exact H.h₀
      h₁ := by
        change SSet.ι₁ ≫ H.h = (F ≫ _) ≫ cosliceEdgeFiberPrecomposition e a _ ha rfl y
        have ht : normalizedCoconeRestrictionFiber e (stdSimplex.δ (0 : Fin 2)) rfl y =
            cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y := by
          simp only [normalizedCoconeRestrictionFiber_eq, eqToHom_refl, Category.comp_id]
        calc
          _ = ((F ≫ cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y) ≫
              cosliceEdgeSectionFiber e y) ≫
                normalizedCoconeRestrictionFiber e (stdSimplex.δ (1 : Fin 2)) ha y := H.h₁
          _ = (F ≫ cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y) ≫
              (cosliceEdgeSectionFiber e y ≫
                normalizedCoconeRestrictionFiber e (stdSimplex.δ (1 : Fin 2)) ha y) :=
            Category.assoc _ _ _
          _ = (F ≫ cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y) ≫
              cosliceEdgeFiberPrecomposition e a _ ha rfl y :=
            congrArg (fun k ↦ (F ≫ cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y) ≫ k)
              (cosliceEdgeSectionFiber_source e a ha y)
          _ = _ := (congrArg (fun k ↦ (F ≫ k) ≫
            cosliceEdgeFiberPrecomposition e a _ ha rfl y) ht).symm
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro z
        exact False.elim z.1.property }

/-- 公開した前合成の比較は、同じ終点固定円柱の始点への raw な射影である。 -/
lemma cosliceEdgeFamilyPrecompositionCylinder_projection :
    (cosliceEdgeFamilyPrecompositionCylinder e y F a b ha hb).h =
      (cosliceEdgeFamilyCylinder e y F).homotopy.h ≫
        normalizedCoconeRestrictionFiber e (stdSimplex.δ (1 : Fin 2)) ha y := by
  cases hb
  rfl

end
end SerrePositivity.InfinityCategories.HomotopyLimits
