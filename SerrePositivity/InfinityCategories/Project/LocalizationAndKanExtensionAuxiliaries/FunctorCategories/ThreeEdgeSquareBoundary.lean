module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.ThreeEdgeSquareComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilySquareInverse

/-!
概要：三辺固定の正方形の比較から右辺の経路を取り出す。
方針：三辺の包含で固定条件を制限し、右辺の両端を下辺・上辺で計算する。
規約：経路は元の正方形全体のホモトピーの制限そのもの。
使われ方：B1 の順方向比較の path と復元側の境界輸送の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

section
variable {A X : SSet.{u}} [Quasicategory X] {U V W : A ⟶ X}
variable {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
variable {d₀ d₁ : SSet.Homotopy U W} {T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀}
variable {Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d₁} (c : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.ThreeEdgeSquareComparison T Q)

/-- 概要：三辺固定の比較は下辺上で恒等関手に定値。
方針：三辺の和への下辺の包含で制限する。
規約：全時間での射の等式。
使われ方：右辺の経路の始点側を固定する。 -/
lemma ThreeEdgeSquareComparison.bottom :
    ((SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u})) ≫
      c.homotopy.h = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) := by
  have h := c.restriction_precomp _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdgesBottom
  change ((SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u})) ≫
    c.homotopy.h = fst _ (Δ[1] : SSet.{u}) ≫ SSet.ι₀ ≫ Q.diagram at h
  simpa only [Q.bottom, SSet.comp_const] using h

/-- 概要：三辺固定の比較は左辺の代表を全時間で保持する。
方針：三辺の和への左辺の包含で制限する。
規約：raw な射の等式。
使われ方：単位成分の固定。 -/
lemma ThreeEdgeSquareComparison.left :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫ c.homotopy.h =
      fst _ (Δ[1] : SSet.{u}) ≫ curry l.h := by
  have h := c.restriction_precomp _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdgesLeft
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫ c.homotopy.h =
    fst _ (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[1] ≫ Q.diagram at h
  simpa only [Q.left] using h

/-- 概要：三辺固定の比較は上辺の代表を全時間で保持する。
方針：三辺の和への上辺の包含で制限する。
規約：raw な射の等式。
使われ方：右辺の経路の終点側を固定する。 -/
lemma ThreeEdgeSquareComparison.top :
    ((SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u})) ≫
      c.homotopy.h = fst _ (Δ[1] : SSet.{u}) ≫ curry r.h := by
  have h := c.restriction_precomp _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.squareThreeEdgesTop
  change ((SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u})) ≫
    c.homotopy.h = fst _ (Δ[1] : SSet.{u}) ≫ SSet.ι₁ ≫ Q.diagram at h
  simpa only [Q.top] using h

/-- 概要：正方形全体の比較の右辺を二変数の図式として取り出す。
方針：右辺の包含と時間との直積で前合成する。
規約：第一座標は辺、第二座標は時間。
使われ方：導来 fiber の path 成分。 -/
noncomputable def ThreeEdgeSquareComparison.rightSquare :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom A).obj X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) ≫ c.homotopy.h

/-- 概要：右辺の経路は指定三角形の対角から始まる。
方針：時間零の自然性と、補完した正方形の右辺の公式を使う。
規約：辺の代表そのものの等式。
使われ方：単位比較の像の回収。 -/
lemma ThreeEdgeSquareComparison.rightSquare_zero :
    SSet.ι₀ ≫ c.rightSquare = curry d₀.h := by
  change _ ≫ ((_ ▷ _) ≫ c.homotopy.h) = _
  rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, c.homotopy.h₀,
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle T).right]

/-- 概要：右辺の経路は元の正方形の右辺で終わる。
方針：時間一の自然性と元の正方形の右辺の公式を使う。
規約：辺の代表そのものの等式。
使われ方：指定 comma 頂点の終辺の回収。 -/
lemma ThreeEdgeSquareComparison.rightSquare_one :
    SSet.ι₁ ≫ c.rightSquare = curry d₁.h := by
  change _ ≫ ((_ ▷ _) ≫ c.homotopy.h) = _
  rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, c.homotopy.h₁, Q.right]

/-- 概要：右辺の経路の始点側は全時間で指定関手に固定される。
方針：右下隅を下辺で計算し、比較の下辺の定値性を使う。
規約：時間方向の恒等辺そのものを保持する。
使われ方：端点固定の写像空間へ持ち上げる。 -/
lemma ThreeEdgeSquareComparison.rightSquare_source :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫ c.rightSquare = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) := by
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u}) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫
          ((SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u})) := by
    apply SSet.yonedaEquiv.injective
    apply Prod.ext
    · apply Prod.ext <;> decide
    · decide
  change _ ≫ ((_ ▷ _) ≫ c.homotopy.h) = _
  rw [← Category.assoc, hv, Category.assoc, c.bottom, SSet.comp_const]

/-- 概要：右辺の経路の終点側は全時間で指定関手に固定される。
方針：右上隅を上辺で計算し、後辺の終点を回収する。
規約：時間方向の恒等辺そのものを保持する。
使われ方：端点固定の写像空間へ持ち上げる。 -/
lemma ThreeEdgeSquareComparison.rightSquare_target :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ c.rightSquare = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex W) := by
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ▷ (Δ[1] : SSet.{u})) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫
          ((SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ▷ (Δ[1] : SSet.{u})) := by
    apply SSet.yonedaEquiv.injective
    apply Prod.ext
    · apply Prod.ext <;> decide
    · decide
  have ht : stdSimplex.δ (0 : Fin 2) ≫ curry r.h = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex W) := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_const]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r).tgt_eq
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ fst _ (Δ[1] : SSet.{u}) =
      stdSimplex.isTerminalObj₀.from Δ[1] ≫ stdSimplex.δ (0 : Fin 2) := by
    apply SSet.yonedaEquiv.injective
    decide
  change _ ≫ ((_ ▷ _) ≫ c.homotopy.h) = _
  rw [← Category.assoc, hv, Category.assoc, c.top, ← Category.assoc, hf,
    Category.assoc, ht, SSet.comp_const]

end

section
variable {A X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌} {V : A ⟶ X}
variable {l : SSet.Homotopy (SSet.const x) V} {r : SSet.Homotopy V (SSet.const y)}
variable {d₀ d₁ : SSet.Homotopy (SSet.const x : A ⟶ X) (SSet.const y)}
variable {T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀} {Q : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionSquare l r d₁}
variable (c : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.ThreeEdgeSquareComparison T Q) (f g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y)
variable (hf : curry d₀.h = curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy f).h)
variable (hg : curry d₁.h = curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy g).h)

/-- 概要：正方形全体の比較の右辺を、元の写像空間の族のホモトピーへ移す。
方針：右辺の正方形の四辺を照合し、端点固定の逆転置を適用する。
規約：新しい path を選ばず、正方形全体の比較から制限した図式を使う。
使われ方：復元側の境界輸送と同じ path を使う順方向比較。 -/
noncomputable def ThreeEdgeSquareComparison.familyHomotopy : SSet.Homotopy f g :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHomotopyOfSquare c.rightSquare (c.rightSquare_zero.trans hf)
    (c.rightSquare_one.trans hg) c.rightSquare_source c.rightSquare_target

/-- 概要：族に移した経路の正方形表示は元の比較の右辺そのもの。
方針：端点固定の逆転置の厳密な回収公式を使う。
規約：ホモトピー類の一致より強い図式の等式。
使われ方：右辺の path と正方形全体の変形の照合。 -/
lemma ThreeEdgeSquareComparison.familyHomotopy_square :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilySquare (c.familyHomotopy f g hf hg) = c.rightSquare :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFamilyHomotopyOfSquare_square _ _ _ _ _

end

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
