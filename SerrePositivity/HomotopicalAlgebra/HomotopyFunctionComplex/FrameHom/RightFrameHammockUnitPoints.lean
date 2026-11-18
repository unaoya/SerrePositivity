module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameHammockComponentImage
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SourceRoofUnitNormalization

/-!
概要：元の通常射を六辺の全比較の各段階で同じ零単体の点として追跡する。
方針：同じ augmentation の前後合成と実 roof の単位収縮を使う。
規約：同じ元の射・同じ六辺を保持し、逆比較の選択と切り離さない。
使われ方：実比較の零単体の正規化と指定二胞体の共役式への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet _root_.Opposite _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.SimplicialModel
open scoped _root_.Simplicial

/-- 概要：単位からの同じ単体写像は元の零単体の定値写像に一致する。
方針：元の自然性を零単体への唯一の作用素へ適用する。
規約：元の全単体を保持。使われ方：実 row 写像と零単体の一致。 -/
lemma unitHom_eq_const {K : SSet.{w}} (f : 𝟙_ SSet.{w} ⟶ K) :
    f = SSet.const (f.app (op ⦋0⦌) PUnit.unit) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  cases x
  have h := ConcreteCategory.congr_hom (f.naturality (n.unop.const ⦋0⦌ 0).op) PUnit.unit
  exact h

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex) (f : X ⟶ Y)

/-- 概要：同じ元の射の零単体を六辺の七段階で追跡する。
方針：同じ right/source augmentation と元の hammock 射の一定単体を並べる。
規約：始点は元の right frame の零単体、終点は元の射そのもの。
使われ方：同じ六辺の零単体三角形。 -/
def rightFrameHammockUnitPoint (i : Fin 7) :
    ((𝟙_ SSet.{max u v}) ⟶ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockFamilyDiagram q r i).obj Y) :=
  match i with
  | 0 => SSet.const (ULift.up (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app Y))
  | 1 => SSet.const (ULift.up (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app Y ≫
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r).obj Y)))
  | 2 => SSet.const (ULift.up (q.augmentation.app ⦋0⦌ ≫
      (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app Y ≫
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r).obj Y))))
  | 3 => SSet.const (ULift.up (q.augmentation.app ⦋0⦌ ≫
      (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app Y)))
  | 4 => SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sourceFrameUnitElement q ⦋0⦌
      (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app Y)))
  | 5 => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (weakEquivalences C) (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app Y)
  | 6 => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (weakEquivalences C) f

/-- 概要：同じ置換単位による第一辺は元の射の同じ零単体を送る。
方針：元の単位の自然性をその同じ成分自身へ適用する。
規約：実写像の厳密な等式。使われ方：六辺の単位追跡。 -/
lemma rightFrameHammockUnitPoint_edge0 :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint q r f 0 ≫ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockFamilyEdge q r 0).app Y =
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint q r f 1 := by
  simp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint]
  rw [SSet.const_comp]
  apply congrArg SSet.const
  apply ULift.ext
  change (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app Y) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r).map ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app Y) = _
  have h := (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).naturality ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app Y)
  exact (Category.assoc _ _ _).trans (congrArg (f ≫ ·) h.symm)

/-- 概要：右混合比較は同じ source augmentation の前合成へ送る。
方針：同じ比較の元の零次成分を読む。
規約：実写像の厳密な等式。使われ方：六辺の単位追跡。 -/
lemma rightFrameHammockUnitPoint_edge1 :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint q r f 1 ≫ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockFamilyEdge q r 1).app Y =
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint q r f 2 := by
  simp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint]
  rw [SSet.const_comp]
  rfl

/-- 概要：左混合比較の元の射は同じ右 augmentation の後合成。
方針：元の全単位三角形の零次成分を結合律で読む。
規約：逆向き辺の元の実写像。使われ方：六辺の単位追跡。 -/
lemma rightFrameHammockUnitPoint_edge2 :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint q r f 3 ≫ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockFamilyEdge q r 2).app Y =
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint q r f 2 := by
  simp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint]
  rw [SSet.const_comp]
  apply congrArg SSet.const
  apply ULift.ext
  change (q.augmentation.app ⦋0⦌ ≫ (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app Y)) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r).obj Y) = _
  simp only [Category.assoc]

/-- 概要：元の全要素 augmentation は同じ source 零単体を回収する。
方針：同じ終端 augmentation の元の零単体公式を使う。
規約：同じ選択次数零。使われ方：実 roof の単位収縮との接続。 -/
lemma rightFrameHammockUnitPoint_edge3 :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint q r f 4 ≫ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockFamilyEdge q r 3).app Y =
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint q r f 3 := by
  simp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint]
  rw [SSet.const_comp]
  apply congrArg SSet.const
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation_zero _ _

/-- 概要：実二列 roof の単位点は反転後に元の合成射の一定全単体へ戻る。
方針：元の roof の零単体照合と同じ実円柱による単位収縮を合成する。
規約：同じ元の比較射。使われ方：選択した逆を含む零単体の正規化。 -/
lemma rightFrameHammockUnitPoint_edge4_Q :
    AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint q r f 4 ≫ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockFamilyEdge q r 4).app Y) =
        AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint q r f 5) := by
  have h : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint q r f 4 ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockFamilyEdge q r 4).app Y =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj (weakEquivalences C) (q.augmentation.app ⦋0⦌)
          (q.augmentation_weakEquivalence ⦋0⦌)
          (q.augmentation.app ⦋0⦌ ≫ (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app Y))) := by
    simp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint]
    rw [SSet.const_comp]
    rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.unitHom_eq_const (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitRowMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj (weakEquivalences C)
      (q.augmentation.app ⦋0⦌) (q.augmentation_weakEquivalence ⦋0⦌)
      (q.augmentation.app ⦋0⦌ ≫ (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app Y))))]
    apply congrArg SSet.const
    exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sourceFrameUnitElement_roof_zero q ⦋0⦌ (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app Y)
  rw [h]
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sourceFrameUnitRoof_Q q ⦋0⦌ (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app Y)

/-- 概要：最後の置換単位による後合成は元の合成射そのもの。
方針：元の二本の forward 射の hammock 合成を回収する。
規約：元の射と同じ終点単位。使われ方：全標的への復帰の零単体。 -/
lemma rightFrameHammockUnitPoint_edge5 :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint q r f 6 ≫ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockFamilyEdge q r 5).app Y =
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint q r f 5 := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  cases x
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardPairComposition.composePoint_arrowPoint (weakEquivalences C) f
    ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app Y) n

/-- 概要：同じ六つの辺は元の射の零単体を各段階で反転後に厳密に追跡する。
方針：五つの実等式と同じ実 roof 収縮をまとめる。
規約：全辺の元の向きを保持。使われ方：逆比較の一意性による合成。 -/
lemma rightFrameHammockUnitPoint_edge_Q (i : Fin 6) :
    AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint q r f (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockEdgeSource i) ≫
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockFamilyEdge q r i).app Y) =
      AnodyneHomotopy.anodyneQ.map
        (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint q r f (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockEdgeTarget i)) := by
  fin_cases i
  · exact congrArg AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint_edge0 q r f)
  · exact congrArg AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint_edge1 q r f)
  · exact congrArg AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint_edge2 q r f)
  · exact congrArg AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint_edge3 q r f)
  · exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint_edge4_Q q r f
  · exact congrArg AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockUnitPoint_edge5 q r f)

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
