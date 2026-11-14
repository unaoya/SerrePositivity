module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.TriangleAppendMissingFace
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape

/-! # 二つのホモトピー三角形による複体の四角形

概要：共通の対角を持つ二つの合成三角形を dg nerve の正方形に貼る。
方針：四辺・対角・二つの次数 −1 原始元をデータとし、正方形の二セル表示を使う。
規約：下の三角形は bottom/right、上は left/top。使われ方：D7 の suspension の射の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded CochainComplex HomComplex
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]

/-- 実際のホモトピーを指定した複体の四角形。 -/
@[ext] structure ComplexSquareData (A B C D : _root_.SerrePositivity.DifferentialGraded.Complex S) where
  bottom : A ⟶ B
  left : A ⟶ C
  right : B ⟶ D
  top : C ⟶ D
  diagonal : A ⟶ D
  lowerHomotopy : Cochain A D (-1)
  upperHomotopy : Cochain A D (-1)
  lowerEquation : δ (-1) 0 lowerHomotopy = Cochain.ofHom (bottom ≫ right) - Cochain.ofHom diagonal
  upperEquation : δ (-1) 0 upperHomotopy = Cochain.ofHom (left ≫ top) - Cochain.ofHom diagonal

namespace ComplexSquareData
variable {A B C D E : _root_.SerrePositivity.DifferentialGraded.Complex S} (s : ComplexSquareData A B C D)

/-- 四角形の下側の二単体。 -/
def lowerTriangle : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) 2 :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct s.bottom s.right s.diagonal s.lowerHomotopy s.lowerEquation).simplex

/-- 四角形の上側の二単体。 -/
def upperTriangle : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) 2 :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct s.left s.top s.diagonal s.upperHomotopy s.upperEquation).simplex

/-- 二つの三角形は対角で一致する。 -/
lemma triangles_compatible :
    SSet.stdSimplex.δ (1 : Fin 3) ≫
        (SSet.yonedaEquiv.symm s.upperTriangle : (Δ[2] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) =
      SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm s.lowerTriangle := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct s.left s.top s.diagonal s.upperHomotopy s.upperEquation).d₁.trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexCompStruct s.bottom s.right s.diagonal s.lowerHomotopy s.lowerEquation).d₁.symm)

/-- 二三角形を貼った実際の単体的四角形。 -/
def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.desc (SSet.yonedaEquiv.symm s.upperTriangle)
    (SSet.yonedaEquiv.symm s.lowerTriangle) s.triangles_compatible

/-- 下側セルへの制限。 -/
lemma square_lower : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ s.square = SSet.yonedaEquiv.symm s.lowerTriangle :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inr_desc _ _ _

/-- 上側セルへの制限。 -/
lemma square_upper : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ≫ s.square = SSet.yonedaEquiv.symm s.upperTriangle :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.inl_desc _ _ _

/-- 終点への鎖写像を四角形の後半二辺とホモトピーに後合成する。 -/
def postcompose (q : D ⟶ E) : ComplexSquareData A B C E where
  bottom := s.bottom
  left := s.left
  right := s.right ≫ q
  top := s.top ≫ q
  diagonal := s.diagonal ≫ q
  lowerHomotopy := s.lowerHomotopy.comp (Cochain.ofHom q) (add_zero (-1))
  upperHomotopy := s.upperHomotopy.comp (Cochain.ofHom q) (add_zero (-1))
  lowerEquation := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangle_postcompose_differential _ _ _ _ s.lowerEquation q
  upperEquation := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexTriangle_postcompose_differential _ _ _ _ s.upperEquation q

/-- 後合成した下側三角形。 -/
lemma postcompose_lower (q : D ⟶ E) :
    (s.postcompose q).lowerTriangle = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.postcomposeComplexTriangle
      s.bottom s.right s.diagonal s.lowerHomotopy s.lowerEquation q := rfl

/-- 後合成した上側三角形。 -/
lemma postcompose_upper (q : D ⟶ E) :
    (s.postcompose q).upperTriangle = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.postcomposeComplexTriangle
      s.left s.top s.diagonal s.upperHomotopy s.upperEquation q := rfl

end ComplexSquareData
end SerrePositivity.InfinityCategories.Project.DerivedCategories
