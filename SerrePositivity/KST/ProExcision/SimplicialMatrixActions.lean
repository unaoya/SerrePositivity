module
public import SerrePositivity.KST.ProExcision.Lemma416SimplicialHomotopy
public import SerrePositivity.KST.ProExcision.MatrixActionCoefficientMap
public import SerrePositivity.KST.ProExcision.ActionMorphisms

/-!
# 単体的イデアルの実群への行列モノイド作用

概要：係数次数ごとの全行列作用を単体的モノイド作用に束ね、右乗法を同変射にする。
方針：係数準同型による作用の自然性と単体環の恒等・合成を使う。
規約：KST Lemma 4.16 の M_{n,n}(I) 同変性、単位化上の全行列を許す。
使われ方：A.4 の作用の界面へ実 m 次比較を渡す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：周囲の単体環上の n×n 行列モノイド。
方針：各次数で全行列を取り、係数写像を面・退化に使う。
規約：KST 4.16、群状であるとは仮定しない。
使われ方：列群と三角ブロック群の共通の外部作用。 -/
def SimplicialIdealData.matrixMonoid (I : SimplicialIdealData.{u}) (n : ℕ) : SimplicialObject MonCat.{u} where
  obj k := MonCat.of (Matrix (Fin n) (Fin n) (I.ambient.obj k))
  map {k l} φ := MonCat.ofHom (I.ambient.map φ).hom.mapMatrix.toMonoidHom
  map_id k := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro M
    ext i j
    change I.ambient.map (𝟙 k) (M i j) = M i j
    rw [I.ambient.map_id]
    rfl
  map_comp {k l s} φ ψ := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro M
    ext i j
    change I.ambient.map (φ ≫ ψ) (M i j) = I.ambient.map ψ (I.ambient.map φ (M i j))
    rw [I.ambient.map_comp]
    rfl

/-- 概要：単体的な列群への全行列モノイド作用。
方針：各次数の idealMatrixAction と係数自然性を使う。
規約：KST 4.16 の Q と始域。使われ方：右乗法の同変射の始域。 -/
def SimplicialIdealData.columnMatrixAction (I : SimplicialIdealData.{u}) (n : ℕ) :
    SimplicialMonoidAction (I.matrixMonoid n) (I.columnGroup n ⋙ forget₂ GrpCat MonCat) where
  action k := idealMatrixAction n (I.ideal k)
  naturality {k l} φ M v := idealMatrixAction_functorial n (I.ideal k) (I.ideal l)
    (I.ambient.map φ).hom (I.map_mem φ) M v

/-- 概要：単体的な実三角ブロック群への全行列モノイド作用。
方針：各次数の実作用と係数自然性を使う。
規約：KST 4.16 の値域 H。使われ方：単体的な同変実ホモトピーの値域の作用。 -/
def SimplicialIdealData.triangularMatrixAction (I : SimplicialIdealData.{u}) (n m : ℕ) :
    SimplicialMonoidAction (I.matrixMonoid n) (I.triangularGroup n m ⋙ forget₂ GrpCat MonCat) where
  action k := triangularBlockMatrixAction n m (I.ideal k)
  naturality {k l} φ M g := triangularBlockMatrixAction_functorial n m (I.ideal k) (I.ideal l)
    (I.ambient.map φ).hom (I.map_mem φ) M g

/-- 概要：単体的イデアル上の右乗法の列は全行列作用に同変な実射。
方針：実群準同型の自然変換と次数ごとの同変性を束ねる。
規約：KST Lemma 4.16 の非可換版 φ(v)=va。
使われ方：A.4 の homologically m-constant の入力となる実射。 -/
def SimplicialIdealData.rightColumnActionHom (I : SimplicialIdealData.{u})
    (a : I.ideal (op ⦋0⦌)) (n m : ℕ) :
    SimplicialActionHom (I.columnMatrixAction n) (I.triangularMatrixAction n (m + 1)) where
  hom := Functor.whiskerRight (I.rightColumnMap a n m) (forget₂ GrpCat MonCat)
  equivariant k M v := lastRightColumnHom_equivariant n m (I.ideal k)
    (I.vertexElement a k : I.ambient.obj k) M v

end SerrePositivity.KST.ProExcision
