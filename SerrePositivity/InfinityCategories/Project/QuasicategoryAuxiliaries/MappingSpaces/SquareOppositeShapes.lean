module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeDiagramReverse
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinReverse
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Square
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.GridOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.StandardJoinOpposite

/-! # 反転した四角形の span と cospan

概要：標準 cospan の錐の反転と標準 span の余錐の形状を比較する。
方針：ホーンの二辺と標準二単体の反転を計算する。
規約：cospan の二辺は反転で交換される。
使われ方：引き戻し四角形を反転した押し出し四角形と同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：span の第一辺は反転した cospan の第二辺。
方針：ホーンの包含を消去して標準二単体の頂点を比較する。
規約：辺の向きも反転。使われ方：第一三角形の照合。 -/
lemma stableHornReverse_two_left :
    horn₂₀.ι₀₁ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso.{u} 2 2).hom =
      (stdSimplex.opIso ⦋1⦌).inv ≫ SSet.opFunctor.map horn₂₂.ι₁₂ := by
  have : Mono (SSet.opFunctor.map (horn 2 (2 : Fin 3)).ι) := by
    change Mono (SSet.opEquivalence.functor.map (horn 2 (2 : Fin 3)).ι)
    infer_instance
  apply (cancel_mono (SSet.opFunctor.map (horn 2 (2 : Fin 3)).ι)).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso_hom_ι]
  apply SSet.yonedaEquiv.injective
  apply SSet.opObjEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 概要：span の第二辺は反転した cospan の第一辺。
方針：ホーンの包含を消去して標準二単体の頂点を比較する。
規約：辺の向きも反転。使われ方：第二三角形の照合。 -/
lemma stableHornReverse_two_right :
    horn₂₀.ι₀₂ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso.{u} 2 2).hom =
      (stdSimplex.opIso ⦋1⦌).inv ≫ SSet.opFunctor.map horn₂₂.ι₀₂ := by
  have : Mono (SSet.opFunctor.map (horn 2 (2 : Fin 3)).ι) := by
    change Mono (SSet.opEquivalence.functor.map (horn 2 (2 : Fin 3)).ι)
    infer_instance
  apply (cancel_mono (SSet.opFunctor.map (horn 2 (2 : Fin 3)).ι)).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso_hom_ι]
  apply SSet.yonedaEquiv.injective
  apply SSet.opObjEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- 概要：標準 span の余錐から反転した標準 cospan の錐への射。
方針：ホーンと零単体を反転し、join の反転同型の逆を使う。
規約：三角形の二脚を交換。使われ方：四角形の普遍性の双対化。 -/
def squareConeReverseShape :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (horn 2 0 : SSet.{u}) Δ[0] ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] (horn 2 2 : SSet.{u})).op :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso 2 2).hom (stdSimplex.opIso ⦋0⦌).inv ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinReverseIso Δ[0] (horn 2 2 : SSet.{u})).inv

/-- 概要：第一余錐三角形は反転した第二錐三角形となる。
方針：ホーンの辺の反転と join 反転の自然性、標準二単体の表示を使う。
規約：脚の番号を交換。使われ方：正方形の反転との照合。 -/
lemma squareConeReverseShape_left :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft ≫ squareConeReverseShape.{u} =
      (stdSimplex.opIso ⦋2⦌).inv ≫ SSet.opFunctor.map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleRight := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft squareConeReverseShape _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleRight
  rw [Category.assoc, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _),
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, stableHornReverse_two_left]
  have hj := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp (stdSimplex.opIso ⦋1⦌).inv
    (SSet.opFunctor.map horn₂₂.ι₁₂) (stdSimplex.opIso ⦋0⦌).inv (𝟙 ((Δ[0] : SSet.{u}).op))
  rw [Category.comp_id] at hj
  rw [hj]
  simp only [Category.assoc]
  have hR := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stableJoinReverse_inv_naturality (𝟙 (Δ[0] : SSet.{u})) horn₂₂.ι₁₂
  simp only [CategoryTheory.Functor.map_id] at hR
  rw [hR, reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableJoinReverse_stdSimplex_zero_one_inv_triangle]
  simp only [CategoryTheory.Functor.map_comp]

/-- 概要：第二余錐三角形は反転した第一錐三角形となる。
方針：ホーンのもう一方の辺について同じ自然性を使う。
規約：脚の番号を交換。使われ方：正方形の反転との照合。 -/
lemma squareConeReverseShape_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight ≫ squareConeReverseShape.{u} =
      (stdSimplex.opIso ⦋2⦌).inv ≫ SSet.opFunctor.map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleLeft := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight squareConeReverseShape _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleLeft
  rw [Category.assoc, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _ _),
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, stableHornReverse_two_right]
  have hj := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp (stdSimplex.opIso ⦋1⦌).inv
    (SSet.opFunctor.map horn₂₂.ι₀₂) (stdSimplex.opIso ⦋0⦌).inv (𝟙 ((Δ[0] : SSet.{u}).op))
  rw [Category.comp_id] at hj
  rw [hj]
  simp only [Category.assoc]
  have hR := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stableJoinReverse_inv_naturality (𝟙 (Δ[0] : SSet.{u})) horn₂₂.ι₀₂
  simp only [CategoryTheory.Functor.map_id] at hR
  rw [hR, reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableJoinReverse_stdSimplex_zero_one_inv_triangle]
  simp only [CategoryTheory.Functor.map_comp]

/-- 概要：正方形の二三角形は両座標の反転で交換される。
方針：二単体の頂点における両座標を比較する。
規約：i は 0 または 1。使われ方：錐の join 反転との一致。 -/
lemma squareTriangle_reverseGrid (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle i ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) =
      (stdSimplex.opIso ⦋2⦌).inv ≫ SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle i.rev) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.opObjEquiv.injective
  apply Prod.ext <;> apply stdSimplex.ext <;> intro j <;>
    fin_cases i <;> fin_cases j <;> rfl

/-- 概要：cospan の錐の反転は span の余錐として正方形の反転に一致する。
方針：二三角形の pushout の普遍性で直前の計算を貼り合わせる。
規約：形状の厳密な等式。使われ方：引き戻し性と反転した押し出し性の同値。 -/
lemma squareConeReverseShape_square :
    squareConeReverseShape ≫ SSet.opFunctor.map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.{u}.hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCocone_isPushout.hom_ext
  · rw [← Category.assoc, squareConeReverseShape_left, Category.assoc,
      ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso_right,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_left, squareTriangle_reverseGrid]
    rfl
  · rw [← Category.assoc, squareConeReverseShape_right, Category.assoc,
      ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso_left,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_right, squareTriangle_reverseGrid]
    rfl

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
