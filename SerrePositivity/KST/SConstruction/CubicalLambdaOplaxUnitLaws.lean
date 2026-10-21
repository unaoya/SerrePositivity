module
public import SerrePositivity.KST.SConstruction.ComonoidPairUnit
public import SerrePositivity.KST.SConstruction.CubicalLambdaTensorMap
public import SerrePositivity.KST.SConstruction.CubicalLambdaCounit
public import SerrePositivity.KST.SConstruction.DGTensorUnitors

/-! # 元の直積と実 dg tensor を比較する Λ の oplax 単位則
概要：元の対角で束ねた二出力の一方を増大し、実 dg 単位関手で他方へ戻る。
方針：元の余モノイド射の増大保存と二出力の左右単位の式を全 Hom で回収する。
規約：元の直積の左右単位と実 dg 単位関手を使う。使われ方：Prop.4.6 の単位則。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の第一出力の増大と実左単位関手の合成を、同じ実 dg 関手として固定する。 -/
def cubicalLambdaTensorPairReduceLeft {M K L : SSet.{u}} (a : M ⟶ K) (b : M ⟶ L) :
    DGFunctor A (CubicalLambda A M) (CubicalLambda A L) :=
  DGFunctor.comp
    (DGFunctor.comp (cubicalLambdaTensorPair A a b)
      (dgTensorFunctor A (cubicalLambdaCounit A K) (DGFunctor.id (CubicalLambda A L))))
    (dgTensorLeftUnitor A (CubicalLambda A L))

/-- 元の第二出力の増大と実右単位関手の合成を、同じ実 dg 関手として固定する。 -/
def cubicalLambdaTensorPairReduceRight {M K L : SSet.{u}} (a : M ⟶ K) (b : M ⟶ L) :
    DGFunctor A (CubicalLambda A M) (CubicalLambda A K) :=
  DGFunctor.comp
    (DGFunctor.comp (cubicalLambdaTensorPair A a b)
      (dgTensorFunctor A (DGFunctor.id (CubicalLambda A K)) (cubicalLambdaCounit A L)))
    (dgTensorRightUnitor A (CubicalLambda A K))

/-- 元の第一出力を増大し実左単位関手で戻すと、元の第二入力 dg 関手へ戻る。 -/
lemma cubicalLambdaTensorPair_left_unit {M K L : SSet.{u}} (a : M ⟶ K) (b : M ⟶ L) :
    cubicalLambdaTensorPairReduceLeft A a b = cubicalLambdaMap A b := by
  refine EnrichedFunctor.ext (Complex A)
    (F := cubicalLambdaTensorPairReduceLeft A a b)
    (G := cubicalLambdaMap A b) (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans (comonoidPair_left_unit
    (cubicalLambdaMapComonoid A a x y) ((cubicalLambdaMap A b).map x y))

/-- 元の第二出力を増大し実右単位関手で戻すと、元の第一入力 dg 関手へ戻る。 -/
lemma cubicalLambdaTensorPair_right_unit {M K L : SSet.{u}} (a : M ⟶ K) (b : M ⟶ L) :
    cubicalLambdaTensorPairReduceRight A a b = cubicalLambdaMap A a := by
  refine EnrichedFunctor.ext (Complex A)
    (F := cubicalLambdaTensorPairReduceRight A a b)
    (G := cubicalLambdaMap A a) (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans (comonoidPair_right_unit
    (P := cubicalLambdaHomComonoid A M x y)
    (Q := cubicalLambdaHomComonoid A L ((cubicalLambdaMap A b).obj x)
      ((cubicalLambdaMap A b).obj y))
    ((cubicalLambdaMap A a).map x y) (cubicalLambdaMapComonoid A b x y))

/-- 元の終対象との直積と実 dg 左単位関手を介した Λ の oplax 左単位則。 -/
lemma cubicalLambdaOplaxTensor_left_unit (K : SSet.{u}) :
    DGFunctor.comp
        (DGFunctor.comp (cubicalLambdaOplaxTensor A (⊤_ SSet.{u}) K)
          (dgTensorFunctor A (cubicalLambdaOplaxUnit A) (DGFunctor.id (CubicalLambda A K))))
        (dgTensorLeftUnitor A (CubicalLambda A K)) =
      cubicalLambdaMap A (Limits.prod.leftUnitor K).hom :=
  cubicalLambdaTensorPair_left_unit A prod.fst prod.snd

/-- 元の終対象との直積と実 dg 右単位関手を介した Λ の oplax 右単位則。 -/
lemma cubicalLambdaOplaxTensor_right_unit (K : SSet.{u}) :
    DGFunctor.comp
        (DGFunctor.comp (cubicalLambdaOplaxTensor A K (⊤_ SSet.{u}))
          (dgTensorFunctor A (DGFunctor.id (CubicalLambda A K)) (cubicalLambdaOplaxUnit A)))
        (dgTensorRightUnitor A (CubicalLambda A K)) =
      cubicalLambdaMap A (Limits.prod.rightUnitor K).hom :=
  cubicalLambdaTensorPair_right_unit A prod.fst prod.snd

end SerrePositivity.KST.SConstruction
