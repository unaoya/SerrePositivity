module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SimplexVertexDetection
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.Pointed
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.PastingShapes
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.StdSimplexProductMap
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.HomotopyEvaluationPath

/-! # 左四角形から外側四角形への比較

概要：長方形の左四角形を、左列を固定したまま外側四角形へ変形する。
方針：横座標の終点を中央から右へ動かす有限順序写像を使う。
規約：縦座標と左列を厳密に保持。使われ方：回転 cofiber 列と接続射の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：左四角形を外側へ動かす長方形内のホモトピーの形状。
方針：左列の横座標を零に保ち、右列の横座標を時間の後続値とする。
規約：時間は最後の因子。使われ方：貼り合わせの普遍余錐の比較。 -/
def pastingLeftToOuterShape : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[1] ⟶ Δ[2] ⊗ Δ[1] where
  app n := ↾fun p => ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexTripleProductMap {
    toFun q := if q.1.1 = 0 then (0 : Fin 3) else q.2.succ
    monotone' := by decide }).app n p, p.1.2)
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro p
    apply Prod.ext
    · apply stdSimplex.ext
      intro j
      rfl
    · rfl

/-- 概要：変形の始点は左四角形の包含。
方針：横座標の二値を計算する。規約：厳密な等号。使われ方：比較の始点。 -/
lemma pastingLeftToOuterShape_zero : SSet.ι₀ ≫ pastingLeftToOuterShape.{u} =
    stdSimplex.δ (2 : Fin 3) ▷ Δ[1] := by
  apply CartesianMonoidalCategory.hom_ext
  all_goals
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    rintro ⟨p, q⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
    fin_cases i <;> fin_cases j <;> rfl

/-- 概要：変形の終点は外側四角形の包含。
方針：横座標の二値を計算する。規約：厳密な等号。使われ方：比較の終点。 -/
lemma pastingLeftToOuterShape_one : SSet.ι₁ ≫ pastingLeftToOuterShape.{u} =
    stdSimplex.δ (1 : Fin 3) ▷ Δ[1] := by
  apply CartesianMonoidalCategory.hom_ext
  all_goals
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    rintro ⟨p, q⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
    fin_cases i <;> fin_cases j <;> rfl

/-- 概要：長方形の左四角形から外側四角形へのホモトピー。
方針：形状の変形を指定長方形の図式で評価する。
規約：値域の quasicategory 性は不要。使われ方：cofiber と suspension の比較。 -/
def pastingLeftToOuterHomotopy {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) where
  h := pastingLeftToOuterShape ≫ F
  h₀ := by rw [← Category.assoc, pastingLeftToOuterShape_zero]; rfl
  h₁ := by rw [← Category.assoc, pastingLeftToOuterShape_one]; rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 概要：比較の形状は左下の頂点を固定する。
方針：有限頂点で座標を計算する。規約：形状の等号。使われ方：始点固定の比較。 -/
lemma pastingLeftToOuterShape_source :
    ((stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      pastingLeftToOuterShape = snd Δ[0] Δ[1] ≫
        SSet.const (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u})) 0 0) := by
  apply CartesianMonoidalCategory.hom_ext
  all_goals
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    rintro ⟨p, q⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
    fin_cases i
    fin_cases j <;> rfl

/-- 概要：比較の形状の右上での道は右四角形の上辺。
方針：有限頂点で座標を計算する。規約：形状の等号。使われ方：第三成分の照合。 -/
lemma pastingLeftToOuterShape_target :
    ((stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge) ▷ (Δ[1] : SSet.{u})) ≫
      pastingLeftToOuterShape = snd Δ[0] Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫
        (stdSimplex.δ (0 : Fin 3) ▷ Δ[1]) := by
  apply CartesianMonoidalCategory.hom_ext
  all_goals
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    rintro ⟨p, q⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
    fin_cases i
    fin_cases j <;> rfl

/-- 概要：左から外側への比較は左下の頂点を全時間で固定する。
方針：形状の始点固定条件を長方形で評価する。
規約：定値の道を厳密に保持。使われ方：接続射の選択独立性。 -/
lemma pastingLeftToOuterHomotopy_source {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    ((stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      (pastingLeftToOuterHomotopy F).h =
        snd Δ[0] Δ[1] ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2) 0 0) := by
  change _ ≫ (pastingLeftToOuterShape ≫ F) = _
  rw [← Category.assoc, pastingLeftToOuterShape_source, Category.assoc, SSet.const_comp]
  rfl

/-- 概要：比較の左四角形の右上の道は右四角形の上辺である。
方針：形状の右上の道を長方形で評価する。
規約：道の一次単体を保持。使われ方：回転後の第二射と接続射の一致。 -/
lemma pastingLeftToOuterHomotopy_target {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    ((stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge) ▷ (Δ[1] : SSet.{u})) ≫
      (pastingLeftToOuterHomotopy F).h =
        snd Δ[0] Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0) := by
  change _ ≫ (pastingLeftToOuterShape ≫ F) = _
  rw [← Category.assoc, pastingLeftToOuterShape_target]
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
