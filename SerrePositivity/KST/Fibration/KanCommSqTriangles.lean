module
public import SerrePositivity.KST.Fibration.KanCommSqEdges
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictConeSimplex

/-!
概要：元の厳密 Kan 四角形の coherent 表示から、上下全二胞体の実射列を回収する。
方針：同じ錐の join 三角形を制限し、公開 strict 錐の全単体公式を適用する。
規約：元の二胞体そのものを計算し、境界二辺やホモトピー類で置き換えない。
使われ方：K-6 c4 の元の商核四角形と指定 Verdier 四角形の全二胞体比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Fibration

variable {P X Y Z : KanObject.{u}}
  {a : P.obj ⟶ X.obj} {b : P.obj ⟶ Y.obj} {f : X.obj ⟶ Z.obj} {g : Y.obj ⟶ Z.obj}
  (sq : CommSq a b f g)

/-- 元の下側二胞体に使う、同じ cospan の左脚の実射列。 -/
def kanCommSqLowerBaseEdge : (Δ[1] : SSet.{u + 1}) ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan)) :=
  horn₂₂.ι₀₂ ≫ CospanShape.strictCospanHornIso.{u, u + 1}.inv

/-- 元の下側二胞体に対応する、元の通常の錐の脚を前置した同じ二射列。 -/
def kanCommSqLowerChain : ComposableArrows KanObject.{u} 2 :=
  ComposableArrows.precomp
    ((SSet.yonedaEquiv kanCommSqLowerBaseEdge).down ⋙
      kanPullbackDiagram (show Y ⟶ Z from g) (show X ⟶ Z from f))
    ((kanCommSqCone sq).π.app ((SSet.yonedaEquiv kanCommSqLowerBaseEdge).down.obj 0))

/-- 元の coherent 四角形の下側全二胞体は、同じ元の通常の錐の二射列の実像。 -/
theorem kanCommSqInfinitySquare_lower :
    squareTriangle 1 ≫ kanCommSqInfinitySquare sq =
      (joinStdSimplexIso 0 1).inv ≫ (pointJoinStdSimplexIso 1).hom ≫
        SSet.yonedaEquiv.symm ((nerveToCoherent KanObject.{u}).app (Opposite.op ⦋2⦌)
          (kanCommSqLowerChain sq)) := by
  have ht : squareTriangle 1 ≫ cospanConeSquareIso.{u + 1}.inv = cospanConeTriangleLeft := by
    rw [← cospanConeSquareIso_left, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (squareTriangle 1 ≫ cospanConeSquareIso.inv) ≫
    (joinMap (𝟙 Δ[0]) CospanShape.strictCospanHornIso.inv ≫
      strictCoherentConeMap (kanCommSqCone sq)) = _
  rw [ht]
  change ((joinStdSimplexIso 0 1).inv ≫ joinMap (𝟙 Δ[0]) horn₂₂.ι₀₂) ≫ _ = _
  rw [Category.assoc, ← Category.assoc (joinMap _ _), ← joinMap_comp, Category.id_comp]
  rw [strictCoherentConeMap_simplex]
  rfl

/-- 下側全二胞体の実射列は、元の下辺と右辺の二射列そのもの。 -/
theorem kanCommSqLowerChain_eq :
    kanCommSqLowerChain sq = ComposableArrows.mk₂
      (show P ⟶ Y from b) (show Y ⟶ Z from g) := by
  refine ComposableArrows.ext_succ rfl ?_ ?_
  · refine ComposableArrows.ext₁ rfl rfl ?_
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change (kanPullbackDiagram (show Y ⟶ Z from g) (show X ⟶ Z from f)).map
      ((SSet.yonedaEquiv kanCommSqLowerBaseEdge).down.map
        (homOfLE (by decide : (0 : Fin 2) ≤ 1))) = _
    have he : (SSet.yonedaEquiv kanCommSqLowerBaseEdge).down.map
        (homOfLE (by decide : (0 : Fin 2) ≤ 1)) = AsSmall.up.map WalkingCospan.Hom.inl := by
      apply ULift.ext
      exact Subsingleton.elim _ _
    rw [he]
    rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/-- 元の下側全二胞体を、同じ二射の標準 coherent 合成二胞体へ厳密に回収する。 -/
theorem kanCommSqInfinitySquare_lower_compStruct :
    squareTriangle 1 ≫ kanCommSqInfinitySquare sq =
      SSet.yonedaEquiv.symm (coherentNerveCompStruct
        (show P ⟶ Y from b) (show Y ⟶ Z from g)).simplex := by
  rw [kanCommSqInfinitySquare_lower, kanCommSqLowerChain_eq]
  have h : (joinStdSimplexIso 0 1).inv ≫ (pointJoinStdSimplexIso 1).hom =
      𝟙 (Δ[2] : SSet.{u + 1}) := by
    simp [pointJoinStdSimplexIso, simplexCastIso]
  rw [← Category.assoc, h, Category.id_comp]
  rfl


/-- 元の上側二胞体に使う、同じ cospan の左脚の実射列。 -/
def kanCommSqUpperBaseEdge : (Δ[1] : SSet.{u + 1}) ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan)) :=
  horn₂₂.ι₁₂ ≫ CospanShape.strictCospanHornIso.{u, u + 1}.inv

/-- 元の上側二胞体に対応する、元の通常の錐の脚を前置した同じ二射列。 -/
def kanCommSqUpperChain : ComposableArrows KanObject.{u} 2 :=
  ComposableArrows.precomp
    ((SSet.yonedaEquiv kanCommSqUpperBaseEdge).down ⋙
      kanPullbackDiagram (show Y ⟶ Z from g) (show X ⟶ Z from f))
    ((kanCommSqCone sq).π.app ((SSet.yonedaEquiv kanCommSqUpperBaseEdge).down.obj 0))

/-- 元の coherent 四角形の上側全二胞体は、同じ元の通常の錐の二射列の実像。 -/
theorem kanCommSqInfinitySquare_upper :
    squareTriangle 0 ≫ kanCommSqInfinitySquare sq =
      (joinStdSimplexIso 0 1).inv ≫ (pointJoinStdSimplexIso 1).hom ≫
        SSet.yonedaEquiv.symm ((nerveToCoherent KanObject.{u}).app (Opposite.op ⦋2⦌)
          (kanCommSqUpperChain sq)) := by
  have ht : squareTriangle 0 ≫ cospanConeSquareIso.{u + 1}.inv = cospanConeTriangleRight := by
    rw [← cospanConeSquareIso_right, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (squareTriangle 0 ≫ cospanConeSquareIso.inv) ≫
    (joinMap (𝟙 Δ[0]) CospanShape.strictCospanHornIso.inv ≫
      strictCoherentConeMap (kanCommSqCone sq)) = _
  rw [ht]
  change ((joinStdSimplexIso 0 1).inv ≫ joinMap (𝟙 Δ[0]) horn₂₂.ι₁₂) ≫ _ = _
  rw [Category.assoc, ← Category.assoc (joinMap _ _), ← joinMap_comp, Category.id_comp]
  rw [strictCoherentConeMap_simplex]
  rfl

/-- 上側全二胞体の実射列は、元の下辺と右辺の二射列そのもの。 -/
theorem kanCommSqUpperChain_eq :
    kanCommSqUpperChain sq = ComposableArrows.mk₂
      (show P ⟶ X from a) (show X ⟶ Z from f) := by
  refine ComposableArrows.ext_succ rfl ?_ ?_
  · refine ComposableArrows.ext₁ rfl rfl ?_
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change (kanPullbackDiagram (show Y ⟶ Z from g) (show X ⟶ Z from f)).map
      ((SSet.yonedaEquiv kanCommSqUpperBaseEdge).down.map
        (homOfLE (by decide : (0 : Fin 2) ≤ 1))) = _
    have he : (SSet.yonedaEquiv kanCommSqUpperBaseEdge).down.map
        (homOfLE (by decide : (0 : Fin 2) ≤ 1)) = AsSmall.up.map WalkingCospan.Hom.inr := by
      apply ULift.ext
      exact Subsingleton.elim _ _
    rw [he]
    rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/-- 元の上側全二胞体を、同じ二射の標準 coherent 合成二胞体へ厳密に回収する。 -/
theorem kanCommSqInfinitySquare_upper_compStruct :
    squareTriangle 0 ≫ kanCommSqInfinitySquare sq =
      SSet.yonedaEquiv.symm (coherentNerveCompStruct
        (show P ⟶ X from a) (show X ⟶ Z from f)).simplex := by
  rw [kanCommSqInfinitySquare_upper, kanCommSqUpperChain_eq]
  have h : (joinStdSimplexIso 0 1).inv ≫ (pointJoinStdSimplexIso 1).hom =
      𝟙 (Δ[2] : SSet.{u + 1}) := by
    simp [pointJoinStdSimplexIso, simplexCastIso]
  rw [← Category.assoc, h, Category.id_comp]
  rfl

end SerrePositivity.KST.Fibration
