module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CospanFiniteKanSquare
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanCospanPointHomotopy
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalReplacementKan
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.F1BKanComplexHomotopyClasses

/-!
概要：有限二入力の指定 Kan path を共通値の path 模型へ、実際の引き戻し内で輸送する。
方針：有限近似の端点固定比較と全境界輸送正方形を引き戻し内へ移して合成する。
規約：輸送先の path は有限模型の指定射の像と厳密に一致する。
使われ方：元の値の path 引き戻しからの Kan 比較の有限持ち上げ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の有限二入力を持つ Kan 引き戻し射を共通値の指定 path 模型へ輸送できる。
方針：二段の全境界正方形を実際の引き戻し内で合成する。
規約：輸送先の全 path と境界の有限模型を保持。使われ方：値への端点固定反映の接続。 -/
lemma cospan_finite_kan_point_transport {K E D H B : SSet.{u}}
    [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : H ⟶ B) [LeftFibration p] (f : E ⟶ H) (g : D ⟶ H)
    [LeftFibration (f ≫ p)] [LeftFibration (g ≫ p)] (u : K ⟶ E) (v : K ⟶ D)
    (H₀ : SSet.Homotopy (u ≫ f ≫ continuousKanReplacementUnit.app H)
      (v ≫ g ≫ continuousKanReplacementUnit.app H)) :
    ∃ b : B _⦋0⦌, ∃ s : K ⟶ vertexFiber (f ≫ p) b,
      ∃ t : K ⟶ vertexFiber (g ≫ p) b, ∃ M : SSet.{u}, ∃ m : K ⨿ K ⟶ M,
      ∃ z : K ⊗ (Δ[1] : SSet.{u}) ⟶ continuousKanReplacement.obj M,
      ∃ w : M ⟶ vertexFiber p b,
        cylinderBoundaryInclusion K ≫ z = m ≫ continuousKanReplacementUnit.app M ∧
        m ≫ w = coprod.desc (s ≫ vertexFiberMap (f ≫ p) p f rfl b)
          (t ≫ vertexFiberMap (g ≫ p) p g rfl b) ∧
        ∃ H₁ : SSet.Homotopy
          ((s ≫ vertexFiberι (f ≫ p) b) ≫ f ≫ continuousKanReplacementUnit.app H)
          ((t ≫ vertexFiberι (g ≫ p) b) ≫ g ≫ continuousKanReplacementUnit.app H),
          H₁.h = z ≫ continuousKanReplacement.map (w ≫ vertexFiberι p b) ∧
          Nonempty (SSet.Homotopy (kanCospanPoint f g u v H₀)
            (kanCospanPoint f g (s ≫ vertexFiberι (f ≫ p) b)
              (t ≫ vertexFiberι (g ≫ p) b) H₁)) := by
  obtain ⟨b, s, t, M, m, q, z, w, Hu, Hv, G, T, _, _, _, hz, hw, hG, hT⟩ :=
    cospan_finite_kan_square p f g u v H₀
  have hG' : (cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫ G.h =
      coprodCylinderMap ((functorHomotopyRefl u).h ≫ f) ((functorHomotopyRefl v).h ≫ g) ≫
        continuousKanReplacementUnit.app H := by
    dsimp only [functorHomotopyRefl]
    simpa only [Category.assoc, coprodCylinderMap_constant] using hG
  obtain ⟨J, hJ, L₀, _, _, _⟩ := kanCospanPoint_homotopy_of_square f g H₀
    (functorHomotopyRefl u) (functorHomotopyRefl v) G hG'
  let T' : SSet.Homotopy J.h (z ≫ continuousKanReplacement.map (w ≫ vertexFiberι p b)) :=
    { h := T.h
      h₀ := by
        change SSet.ι₀ ≫ T.h = J.h
        rw [T.h₀, hJ]
      h₁ := T.h₁
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  obtain ⟨H₁, h₁, L₁, _, _, _⟩ := kanCospanPoint_homotopy_of_square f g J Hu Hv T' hT
  refine ⟨b, s, t, M, m, z, w, hz, hw, H₁, h₁, ?_⟩
  apply (functorVertex_piZero_eq_iff_homotopy _ _).1
  exact ((functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨L₀⟩).trans
    ((functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨L₁⟩)

end SerrePositivity.InfinityCategories.F2
