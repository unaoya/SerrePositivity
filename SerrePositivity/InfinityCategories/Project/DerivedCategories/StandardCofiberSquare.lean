module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberHomCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComplexTriangles
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
public import SerrePositivity.HomologicalAlgebra.Complex.Basic

/-! # 標準 cofiber 四角形と join 余錐

概要：span の二射の差の mapping cone を頂点とする四角形を構成する。
方針：標準の次数 -1 の包含を一つの三角形のホモトピーとし、もう一方を零として貼る。
規約：底辺は f、左辺は g。使われ方：D7 の coslice による押し出し性の証明の対象。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial

/-- 概要：下三角形の最初の辺は正方形の底辺。
方針：Yoneda で二座標の有限写像を計算する。
規約：三角形一の面 δ₂。使われ方：span の最初の辺の照合。 -/
lemma cofiberSquareTriangle_bottomEdge :
    SSet.stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

/-- 概要：上三角形の最初の辺は正方形の左辺。
方針：Yoneda で二座標の有限写像を計算する。
規約：三角形零の面 δ₂。使われ方：span の第二の辺の照合。 -/
lemma cofiberSquareTriangle_leftEdge :
    SSet.stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge := by
  apply SSet.yonedaEquiv.injective
  apply Prod.ext <;> decide

variable {S : Type u} [CommRing S] {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 概要：span の二射の差を二項直和への鎖写像にする。
方針：第一成分 f、第二成分 -g の射を取る。
規約：零次数の鎖写像。使われ方：標準 cofiber の入力。 -/
def cofiberDifference (f : A ⟶ B) (g : A ⟶ C) : A ⟶ B ⊞ C := biprod.lift f (-g)

/-- 概要：標準の押し出し候補は差の射の mapping cone。
方針：二項直和への差の鎖写像の cone を取る。
規約：まだ普遍性は主張しない。使われ方：cofiber 余錐の頂点。 -/
abbrev pushoutCofiber (f : A ⟶ B) (g : A ⟶ C) : Complex S := mappingCone (cofiberDifference f g)

/-- 概要：B から標準 cofiber への包含。
方針：直和の第一包含と mapping cone の標準包含を合成する。
規約：鎖写像。使われ方：四角形の右辺。 -/
def pushoutInclusionB (f : A ⟶ B) (g : A ⟶ C) : B ⟶ pushoutCofiber f g :=
  biprod.inl ≫ mappingCone.inr (cofiberDifference f g)

/-- 概要：C から標準 cofiber への包含。
方針：直和の第二包含と mapping cone の標準包含を合成する。
規約：鎖写像。使われ方：四角形の上辺。 -/
def pushoutInclusionC (f : A ⟶ B) (g : A ⟶ C) : C ⟶ pushoutCofiber f g :=
  biprod.inr ≫ mappingCone.inr (cofiberDifference f g)

/-- 概要：標準四角形の対角は C を通る厳密な合成。
方針：g の後に C の包含を合成する。
規約：対角を二つの三角形で共有する。使われ方：四角形の貼り合わせ。 -/
def pushoutDiagonal (f : A ⟶ B) (g : A ⟶ C) : A ⟶ pushoutCofiber f g :=
  g ≫ pushoutInclusionC f g

/-- 概要：cone の次数 -1 の包含の微分は四角形の二つの合成の差。
方針：標準包含の微分式を二項直和への射の二成分に展開する。
規約：B 側の合成から C 側の対角を引く。使われ方：下側三角形の dg nerve 方程式。 -/
lemma pushoutHomotopy_differential (f : A ⟶ B) (g : A ⟶ C) :
    δ (-1) 0 (mappingCone.inl (cofiberDifference f g)) =
      Cochain.ofHom (f ≫ pushoutInclusionB f g) - Cochain.ofHom (pushoutDiagonal f g) := by
  rw [mappingCone.δ_inl]
  simp only [cofiberDifference, pushoutInclusionB, pushoutInclusionC, pushoutDiagonal,
    biprod.lift_eq, Preadditive.add_comp, Preadditive.neg_comp, Category.assoc,
    Cochain.ofHom_add, Cochain.ofHom_neg, sub_eq_add_neg]

/-- 概要：B を通る三角形は mapping cone の標準ホモトピーを持つ。
方針：次数 -1 の包含を合成の差の原始元として使う。
規約：第一辺は f。使われ方：標準四角形の下側の二単体。 -/
def cofiberLowerTriangle (f : A ⟶ B) (g : A ⟶ C) :
    SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (pushoutInclusionB f g))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (pushoutDiagonal f g)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct _ _ _ (mappingCone.inl (cofiberDifference f g))
    (pushoutHomotopy_differential f g)

/-- 概要：C を通る三角形は零ホモトピーを持つ。
方針：対角が C を通る厳密な合成であることを使う。
規約：第一辺は g。使われ方：標準四角形の上側の二単体。 -/
def cofiberUpperTriangle (f : A ⟶ B) (g : A ⟶ C) :
    SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge g) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (pushoutInclusionC f g))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (pushoutDiagonal f g)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct _ _ _ 0 (by simp only [δ_zero, pushoutDiagonal, sub_self])

/-- 概要：span と cone の二つの三角形を標準四角形へ貼る。
方針：正方形の二三角形表示の pushout を使う。
規約：この段階では押し出し性をまだ主張しない。使われ方：D7 の余錐の直接充填。 -/
def standardCofiberSquare (f : A ⟶ B) (g : A ⟶ C) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc (SSet.yonedaEquiv.symm (cofiberUpperTriangle f g).simplex)
    (SSet.yonedaEquiv.symm (cofiberLowerTriangle f g).simplex) (by
      rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
        (cofiberUpperTriangle f g).d₁, (cofiberLowerTriangle f g).d₁])

/-- 概要：標準 cofiber 四角形の上側は指定した上三角形。
方針：pushout の第一包含で降下を評価する。
規約：厳密な射の等式。使われ方：各辺の計算。 -/
lemma standardCofiberSquare_upper (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberUpperTriangle f g).simplex := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc _ _ _

/-- 概要：標準 cofiber 四角形の下側は指定した下三角形。
方針：pushout の第二包含で降下を評価する。
規約：厳密な射の等式。使われ方：各辺の計算。 -/
lemma standardCofiberSquare_lower (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberLowerTriangle f g).simplex := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc _ _ _

/-- 概要：標準 cofiber 四角形の底辺は元の f。
方針：下三角形の最初の辺を計算する。
規約：底辺を厳密に保つ。使われ方：cofiber 四角形の入力辺。 -/
lemma standardCofiberSquare_bottom (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge f).edge := by
  rw [← cofiberSquareTriangle_bottomEdge, Category.assoc, standardCofiberSquare_lower,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (cofiberLowerTriangle f g).d₂]

/-- 概要：標準 cofiber 四角形の左辺は元の g。
方針：上三角形の最初の辺を計算する。
規約：左辺を厳密に保つ。使われ方：span の照合。 -/
lemma standardCofiberSquare_left (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge g).edge := by
  rw [← cofiberSquareTriangle_leftEdge, Category.assoc, standardCofiberSquare_upper,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (cofiberUpperTriangle f g).d₂]

/-- 概要：標準 cofiber 四角形の右辺は B の包含。
方針：下三角形の最後の辺を計算する。
規約：鎖写像の包含の辺。使われ方：cofiber 列の第二射。 -/
lemma standardCofiberSquare_right (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (pushoutInclusionB f g)).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge, Category.assoc, standardCofiberSquare_lower,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (cofiberLowerTriangle f g).d₀]

/-- 概要：標準 cofiber 四角形の上辺は C の包含。
方針：上三角形の最後の辺を計算する。
規約：鎖写像の包含の辺。使われ方：余錐の第二の脚。 -/
lemma standardCofiberSquare_top (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (pushoutInclusionC f g)).edge := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_topEdge, Category.assoc, standardCofiberSquare_upper,
    SSet.stdSimplex.δ_comp_yonedaEquiv_symm, (cofiberUpperTriangle f g).d₀]

/-- 概要：標準 cofiber 四角形を join 余錐として読む。
方針：正方形と span の join 余錐の比較を使う。
規約：始対象性は後続で直接証明する。使われ方：coslice の指定始対象候補。 -/
def standardCofiberCocone (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare f g)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
