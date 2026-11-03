module
public import SerrePositivity.InfinityCategories.Derived.TriangleAppendMissingFace
public import SerrePositivity.InfinityCategories.Core.PushoutShape

/-! # 二つのホモトピー三角形による複体の四角形

概要：共通の対角を持つ二つの合成三角形を dg nerve の正方形に貼る。
方針：四辺・対角・二つの次数 −1 原始元をデータとし、正方形の二セル表示を使う。
規約：下の三角形は bottom/right、上は left/top。使われ方：D7 の suspension の射の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve CochainComplex HomComplex
open scoped Simplicial
variable {S : Type u} [CommRing S]

/-- 実際のホモトピーを指定した複体の四角形。 -/
@[ext] structure ComplexSquareData (A B C D : Complex S) where
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
variable {A B C D E : Complex S} (s : ComplexSquareData A B C D)

/-- 四角形の下側の二単体。 -/
def lowerTriangle : Simplex S (Complex S) 2 :=
  (complexCompStruct s.bottom s.right s.diagonal s.lowerHomotopy s.lowerEquation).simplex

/-- 四角形の上側の二単体。 -/
def upperTriangle : Simplex S (Complex S) 2 :=
  (complexCompStruct s.left s.top s.diagonal s.upperHomotopy s.upperEquation).simplex

/-- 二つの三角形は対角で一致する。 -/
lemma triangles_compatible :
    SSet.stdSimplex.δ (1 : Fin 3) ≫
        (SSet.yonedaEquiv.symm s.upperTriangle : (Δ[2] : SSet.{u + 1}) ⟶ dgNerve S (Complex S)) =
      SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm s.lowerTriangle := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm
    ((complexCompStruct s.left s.top s.diagonal s.upperHomotopy s.upperEquation).d₁.trans
      (complexCompStruct s.bottom s.right s.diagonal s.lowerHomotopy s.lowerEquation).d₁.symm)

/-- 二三角形を貼った実際の単体的四角形。 -/
def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ dgNerve S (Complex S) :=
  square_isPushout.desc (SSet.yonedaEquiv.symm s.upperTriangle)
    (SSet.yonedaEquiv.symm s.lowerTriangle) s.triangles_compatible

/-- 下側セルへの制限。 -/
lemma square_lower : squareTriangle 1 ≫ s.square = SSet.yonedaEquiv.symm s.lowerTriangle :=
  square_isPushout.inr_desc _ _ _

/-- 上側セルへの制限。 -/
lemma square_upper : squareTriangle 0 ≫ s.square = SSet.yonedaEquiv.symm s.upperTriangle :=
  square_isPushout.inl_desc _ _ _

/-- 終点への鎖写像を四角形の後半二辺とホモトピーに後合成する。 -/
def postcompose (q : D ⟶ E) : ComplexSquareData A B C E where
  bottom := s.bottom
  left := s.left
  right := s.right ≫ q
  top := s.top ≫ q
  diagonal := s.diagonal ≫ q
  lowerHomotopy := s.lowerHomotopy.comp (Cochain.ofHom q) (add_zero (-1))
  upperHomotopy := s.upperHomotopy.comp (Cochain.ofHom q) (add_zero (-1))
  lowerEquation := complexTriangle_postcompose_differential _ _ _ _ s.lowerEquation q
  upperEquation := complexTriangle_postcompose_differential _ _ _ _ s.upperEquation q

/-- 後合成した下側三角形。 -/
lemma postcompose_lower (q : D ⟶ E) :
    (s.postcompose q).lowerTriangle = postcomposeComplexTriangle
      s.bottom s.right s.diagonal s.lowerHomotopy s.lowerEquation q := rfl

/-- 後合成した上側三角形。 -/
lemma postcompose_upper (q : D ⟶ E) :
    (s.postcompose q).upperTriangle = postcomposeComplexTriangle
      s.left s.top s.diagonal s.upperHomotopy s.upperEquation q := rfl

end ComplexSquareData
end SerrePositivity.InfinityCategories
