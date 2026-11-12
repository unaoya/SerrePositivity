module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingComparisonHomotopy

/-! # 外側四角形から右四角形への比較

概要：長方形の外側を右側の四角形へ変形し、右上を固定して始点を第一の下辺に沿って動かす。
方針：横座標の左端を零から一へ、右端を二に固定する有限順序写像を使う。
規約：縦座標は保つ。使われ方：回転接続射と懸垂の第一射への作用の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：外側四角形を右側へ動かす形状。
方針：右列を二に保ち、左列を時刻の零・一で動かす。
規約：時刻は最後の因子。使われ方：始点が動き右上が固定される比較。 -/
def pastingOuterToRightShape : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[1] ⟶ Δ[2] ⊗ Δ[1] where
  app n := ↾fun p => ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.stdSimplexTripleProductMap {
    toFun q := if q.1.1 = 0 then q.2.castSucc else (2 : Fin 3)
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

/-- 概要：比較形状の始点は外側四角形。
方針：有限頂点で横座標を計算する。
規約：厳密な形状の等号。使われ方：ホモトピーの先頭。 -/
lemma pastingOuterToRightShape_zero : SSet.ι₀ ≫ pastingOuterToRightShape.{u} =
    stdSimplex.δ (1 : Fin 3) ▷ Δ[1] := by
  apply CartesianMonoidalCategory.hom_ext
  all_goals
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    rintro ⟨p, q⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
    fin_cases i <;> fin_cases j <;> rfl

/-- 概要：比較形状の終点は右四角形。
方針：有限頂点で横座標を計算する。
規約：厳密な形状の等号。使われ方：ホモトピーの終端。 -/
lemma pastingOuterToRightShape_one : SSet.ι₁ ≫ pastingOuterToRightShape.{u} =
    stdSimplex.δ (0 : Fin 3) ▷ Δ[1] := by
  apply CartesianMonoidalCategory.hom_ext
  all_goals
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    rintro ⟨p, q⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
    fin_cases i <;> fin_cases j <;> rfl

/-- 概要：長方形の外側四角形から右四角形へのホモトピー。
方針：形状を長方形の図式で評価する。
規約：値域への仮定なし。使われ方：回転接続射の懸垂図式での表示。 -/
def pastingOuterToRightHomotopy {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0) where
  h := pastingOuterToRightShape ≫ F
  h₀ := by rw [← Category.assoc, pastingOuterToRightShape_zero]; rfl
  h₁ := by rw [← Category.assoc, pastingOuterToRightShape_one]; rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

/-- 概要：比較形状の左下の道は左四角形の下辺。
方針：有限頂点で座標を比較する。
規約：始点を固定しない。使われ方：元の第一射の保持。 -/
lemma pastingOuterToRightShape_source :
    ((stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      pastingOuterToRightShape = CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (stdSimplex.δ (2 : Fin 3) ▷ Δ[1]) := by
  apply CartesianMonoidalCategory.hom_ext
  all_goals
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    rintro ⟨p, q⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
    fin_cases i
    fin_cases j <;> rfl

/-- 概要：比較形状は右上を時刻に関して固定する。
方針：有限頂点で両座標を計算する。
規約：外側四角形の右上への定値道。使われ方：比較の終点成分が恒等となる計算。 -/
lemma pastingOuterToRightShape_target :
    ((stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge) ▷ (Δ[1] : SSet.{u})) ≫
      pastingOuterToRightShape = CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫
        SSet.const (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) 1 1) := by
  apply CartesianMonoidalCategory.hom_ext
  all_goals
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    rintro ⟨p, q⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
    fin_cases i
    fin_cases j <;> rfl

/-- 概要：外側から右への比較の始点の道は左下辺そのもの。
方針：形状の式を長方形で評価する。
規約：一次単体を厳密に保つ。使われ方：元の第一射の懸垂への作用。 -/
lemma pastingOuterToRightHomotopy_source {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    ((stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      (pastingOuterToRightHomotopy F).h =
        CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 2 := by
  change _ ≫ (pastingOuterToRightShape ≫ F) = _
  rw [← Category.assoc, pastingOuterToRightShape_source]
  rfl

/-- 概要：外側から右への比較は長方形の右上の頂点を固定する。
方針：形状の固定式を図式で評価する。
規約：値域への仮定なし。使われ方：接続射の合成で恒等成分を消去する。 -/
lemma pastingOuterToRightHomotopy_target {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    ((stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge) ▷ (Δ[1] : SSet.{u})) ≫
      (pastingOuterToRightHomotopy F).h =
        CartesianMonoidalCategory.snd Δ[0] Δ[1] ≫
          SSet.const (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) 1 1) := by
  change _ ≫ (pastingOuterToRightShape ≫ F) = _
  rw [← Category.assoc, pastingOuterToRightShape_target, Category.assoc, SSet.const_comp]
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
