module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TetrahedronFamilyFilling
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity

/-!
概要：指定の二胞体族と二つの厳密合成面を同時に保持する三単体族。
方針：合成三角形の面を計算して内ホーンを貼り、任意のパラメーターを保って充填する。
規約：これは三面の回収まで。欠面の全 native Hom の一致は主張しない。
使われ方：Ind-S (9b) の三面部分の実構成。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 合成三角形をパラメーターに定値に拡張しても、指定第一辺を厳密に回収する。 -/
lemma compStructFamily_first {X : SSet.{u}} {x y z : X _⦋0⦌}
    {e : X.Edge x y} {f : X.Edge y z} {g : X.Edge x z}
    (c : SSet.Edge.CompStruct e f g) (K : SSet.{u}) :
    (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ fst (Δ[2] : SSet.{u}) K ≫
      SSet.yonedaEquiv.symm c.simplex =
      fst (Δ[1] : SSet.{u}) K ≫ SSet.yonedaEquiv.symm e.edge := by
  rw [← Category.assoc, whiskerRight_fst, Category.assoc,
    stdSimplex.δ_comp_yonedaEquiv_symm, c.d₂]

/-- 同じ定値族の第二辺の厳密回収。 -/
lemma compStructFamily_last {X : SSet.{u}} {x y z : X _⦋0⦌}
    {e : X.Edge x y} {f : X.Edge y z} {g : X.Edge x z}
    (c : SSet.Edge.CompStruct e f g) (K : SSet.{u}) :
    (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ fst (Δ[2] : SSet.{u}) K ≫
      SSet.yonedaEquiv.symm c.simplex =
      fst (Δ[1] : SSet.{u}) K ≫ SSet.yonedaEquiv.symm f.edge := by
  rw [← Category.assoc, whiskerRight_fst, Category.assoc,
    stdSimplex.δ_comp_yonedaEquiv_symm, c.d₀]

/-- 同じ定値族の指定合成辺の厳密回収。 -/
lemma compStructFamily_composite {X : SSet.{u}} {x y z : X _⦋0⦌}
    {e : X.Edge x y} {f : X.Edge y z} {g : X.Edge x z}
    (c : SSet.Edge.CompStruct e f g) (K : SSet.{u}) :
    (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ fst (Δ[2] : SSet.{u}) K ≫
      SSet.yonedaEquiv.symm c.simplex =
      fst (Δ[1] : SSet.{u}) K ≫ SSet.yonedaEquiv.symm g.edge := by
  rw [← Category.assoc, whiskerRight_fst, Category.assoc,
    stdSimplex.δ_comp_yonedaEquiv_symm, c.d₁]

/-- 因子分解の同じ三面を厳密に保持する三単体族。全 native Hom の追加制御は含めない。 -/
lemma factorizationTetrahedronFamily_faces
    (X₀ X₁ X₂ X₃ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
    (K : SSet.{u + 1}) (T : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hfirst : (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ T =
      fst (Δ[1] : SSet.{u + 1}) K ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (f ≫ g)).edge)
    (hlast : (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ T =
      fst (Δ[1] : SSet.{u + 1}) K ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge h).edge) :
    ∃ F : (Δ[3] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u},
      (stdSimplex.δ (0 : Fin 4) ▷ K) ≫ F =
        fst (Δ[2] : SSet.{u + 1}) K ≫
          SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct g h).simplex ∧
      (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ F = T ∧
      (stdSimplex.δ (3 : Fin 4) ▷ K) ≫ F =
        fst (Δ[2] : SSet.{u + 1}) K ≫
          SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g).simplex := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronFamily_exists K _ T _
  · erw [compStructFamily_composite, hfirst]
    rfl
  · erw [compStructFamily_first, compStructFamily_last]
  · erw [compStructFamily_last, hlast]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
