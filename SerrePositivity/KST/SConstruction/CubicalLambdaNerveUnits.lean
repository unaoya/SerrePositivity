module
public import SerrePositivity.KST.SConstruction.CubicalLambdaFunctorPairCoherence
public import SerrePositivity.KST.SConstruction.CubicalLambdaNerveMap

/-! # Λ nerve の元の増大による左右単位挿入
概要：一対象 dg 圏の対象宇宙を変えず、左右の tensor 単位を単体的に挿入する。
方針：元の増大と実関手を対角で組にし、全入力自然性と左右単位を使う。
規約：元の一対象 A と元の全 Hom を保持。使われ方：native tensor 比較の単位則。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 元の Λ の増大を左出力として、実 tensor の単位を単体的に挿入する。 -/
def cubicalLambdaNerveUnitLeft :
    cubicalLambdaNerve A D ⟶ cubicalLambdaNerve A (DGTensorCategory A PUnit.{1} D) where
  app n := ↾fun F => cubicalLambdaFunctorPair A
    (cubicalLambdaCounit A (SSet.stdSimplex.obj n.unop)) F
  naturality X Y f := by
    ext F
    have h := cubicalLambdaFunctorPair_precompose A (SSet.stdSimplex.map f.unop)
      (cubicalLambdaCounit A (SSet.stdSimplex.obj X.unop)) F
    rw [cubicalLambdaCounit_naturality] at h
    exact h

/-- 元の Λ の増大を右出力として、実 tensor の単位を単体的に挿入する。 -/
def cubicalLambdaNerveUnitRight :
    cubicalLambdaNerve A D ⟶ cubicalLambdaNerve A (DGTensorCategory A D PUnit.{1}) where
  app n := ↾fun F => cubicalLambdaFunctorPair A F
    (cubicalLambdaCounit A (SSet.stdSimplex.obj n.unop))
  naturality X Y f := by
    ext F
    have h := cubicalLambdaFunctorPair_precompose A (SSet.stdSimplex.map f.unop) F
      (cubicalLambdaCounit A (SSet.stdSimplex.obj X.unop))
    rw [cubicalLambdaCounit_naturality] at h
    exact h

/-- 元の左単位挿入は、実左単位 dg 関手の後合成で恒等を回収する。 -/
lemma cubicalLambdaNerveUnitLeft_unitor :
    cubicalLambdaNerveUnitLeft A D ≫ cubicalLambdaNerveMap A (dgTensorLeftUnitor A D) =
      𝟙 (cubicalLambdaNerve A D) := by
  ext n F
  exact cubicalLambdaFunctorPair_left_unit A F

/-- 元の右単位挿入は、実右単位 dg 関手の後合成で恒等を回収する。 -/
lemma cubicalLambdaNerveUnitRight_unitor :
    cubicalLambdaNerveUnitRight A D ≫ cubicalLambdaNerveMap A (dgTensorRightUnitor A D) =
      𝟙 (cubicalLambdaNerve A D) := by
  ext n F
  exact cubicalLambdaFunctorPair_right_unit A F

end SerrePositivity.KST.SConstruction
