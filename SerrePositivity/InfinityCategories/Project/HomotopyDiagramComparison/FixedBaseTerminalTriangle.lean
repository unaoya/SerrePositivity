module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.HomotopyTriangleClasses
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeInternalHomTrivialFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

/-!
概要：同じ終点へ向かう指定済み二円柱を、底の族を固定して二面に保つ三角形を構成する。
方針：二番目ホーンに二円柱を貼り、自明 Kan fibration の単射持ち上げを使う。
規約：二円柱の raw な射を保持する。使われ方：左右の native 共通脚比較の高次整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
private lemma targetFace (X : SSet.{u}) :
    X ◁ stdSimplex.δ (0 : Fin 2) = fst X (Δ[0] : SSet.{u}) ≫ SSet.ι₁ := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  apply Prod.ext
  · rfl
  · apply stdSimplex.ext
    intro k
    have ht : t k = 0 := Fin.eq_zero (t k)
    change (SimplexCategory.δ (0 : Fin 2)).toOrderHom (t k) = 1
    rw [ht]
    rfl

variable {E B T : SSet.{u}} (q : E ⟶ B) (v : T ⟶ B) {a b s : T ⟶ E}
  (H₀ : SSet.Homotopy a s) (H₁ : SSet.Homotopy b s)

/-- 同じ終点を持つ指定円柱を二面に保ち、底の族を全三角形で固定するデータ。 -/
structure FixedBaseTerminalTriangle where
  family : T ⊗ (Δ[2] : SSet.{u}) ⟶ E
  diagonal : (T ◁ stdSimplex.δ (1 : Fin 3)) ≫ family = H₀.h
  second : (T ◁ stdSimplex.δ (0 : Fin 3)) ≫ family = H₁.h
  base : family ≫ q = fst T (Δ[2] : SSet.{u}) ≫ v

/-- 自明 Kan fibration 上で、二つの指定終端円柱を保つ三角形を構成する。 -/
def fixedBaseTerminalTriangle [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q]
    (h₀ : H₀.h ≫ q = fst T (Δ[1] : SSet.{u}) ≫ v)
    (h₁ : H₁.h ≫ q = fst T (Δ[1] : SSet.{u}) ≫ v) :
    FixedBaseTerminalTriangle q v H₀ H₁ :=
  Classical.choice (by
    let po := horn₂₂.isPushout.map (tensorLeft T)
    have hz : (T ◁ stdSimplex.δ (0 : Fin 2)) ≫ H₀.h =
        (T ◁ stdSimplex.δ (0 : Fin 2)) ≫ H₁.h := by
      rw [targetFace T, Category.assoc, Category.assoc, H₀.h₁, H₁.h₁]
    let W := po.desc H₀.h H₁.h hz
    have hleft : (T ◁ horn₂₂.ι₀₂) ≫ W = H₀.h := po.inl_desc _ _ _
    have hright : (T ◁ horn₂₂.ι₁₂) ≫ W = H₁.h := po.inr_desc _ _ _
    have hW : W ≫ q = fst T (horn 2 2) ≫ v := by
      apply po.hom_ext
      · change (T ◁ horn₂₂.ι₀₂) ≫ (W ≫ _) = (T ◁ horn₂₂.ι₀₂) ≫ _
        rw [← Category.assoc, hleft, h₀, ← Category.assoc, whiskerLeft_fst]
      · change (T ◁ horn₂₂.ι₁₂) ≫ (W ≫ _) = (T ◁ horn₂₂.ι₁₂) ≫ _
        rw [← Category.assoc, hright, h₁, ← Category.assoc, whiskerLeft_fst]
    have : Mono (T ◁ (horn 2 2).ι) := (tensorLeft T).map_mono _
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := q) (T ◁ (horn 2 2).ι) inferInstance
    let sq : CommSq W (T ◁ (horn 2 2).ι) q (fst T (Δ[2] : SSet.{u}) ≫ v) :=
      ⟨by rw [hW, ← Category.assoc, whiskerLeft_fst]⟩
    refine ⟨⟨sq.lift, ?_, ?_, sq.fac_right⟩⟩
    · have h := congrArg (fun k ↦ (T ◁ horn₂₂.ι₀₂) ≫ k) sq.fac_left
      rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, horn.ι_ι] at h
      exact h.trans hleft
    · have h := congrArg (fun k ↦ (T ◁ horn₂₂.ι₁₂) ≫ k) sq.fac_left
      rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, horn.ι_ι] at h
      exact h.trans hright)

variable (D : FixedBaseTerminalTriangle q v H₀ H₁)

/-- 同じ三角形の第一辺は、二つの指定円柱の始点を結ぶ実際の円柱。 -/
def fixedBaseTerminalTriangleFirst : SSet.Homotopy a b where
  h := (T ◁ stdSimplex.δ (2 : Fin 3)) ≫ D.family
  h₀ := by
    change SSet.ι₀ ≫ ((T ◁ stdSimplex.δ (2 : Fin 3)) ≫ D.family) = a
    have hi : SSet.ι₀ ≫ (T ◁ stdSimplex.δ (2 : Fin 3)) =
        SSet.ι₀ ≫ (T ◁ stdSimplex.δ (1 : Fin 3)) := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      apply Prod.ext
      · rfl
      · apply stdSimplex.ext
        intro k
        rfl
    rw [← Category.assoc, hi, Category.assoc, D.diagonal]
    exact H₀.h₀
  h₁ := by
    change SSet.ι₁ ≫ ((T ◁ stdSimplex.δ (2 : Fin 3)) ≫ D.family) = b
    have hi : SSet.ι₁ ≫ (T ◁ stdSimplex.δ (2 : Fin 3)) =
        SSet.ι₀ ≫ (T ◁ stdSimplex.δ (0 : Fin 3)) := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      apply Prod.ext
      · rfl
      · apply stdSimplex.ext
        intro k
        rfl
    rw [← Category.assoc, hi, Category.assoc, D.second]
    exact H₁.h₀
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 第一辺も底を全時刻で固定する。 -/
lemma fixedBaseTerminalTriangleFirst_base :
    (fixedBaseTerminalTriangleFirst q v H₀ H₁ D).h ≫ q =
      fst T (Δ[1] : SSet.{u}) ≫ v := by
  rw [fixedBaseTerminalTriangleFirst, Category.assoc, D.base,
    ← Category.assoc, whiskerLeft_fst]

/-- 指定した元の二円柱と第一辺の類は、実際の三角形による合成等式を満たす。 -/
lemma fixedBaseTerminalTriangle_homMk_comp [Quasicategory E] :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (fixedBaseTerminalTriangleFirst q v H₀ H₁ D)) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₁) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H₀) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyTriangle_homMk_comp _ _ _ D.family rfl D.second D.diagonal

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
