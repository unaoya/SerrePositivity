module
public import SerrePositivity.KST.SConstruction.CubicalLambdaTriplePair
public import SerrePositivity.KST.SConstruction.EnrichedFunctorCompositionLaws

/-! # 元の直積と実 dg tensor を比較する Λ の oplax 結合則
概要：元の三重直積の結合同型と元の dg tensor の結合関手を介して二つの合成を照合する。
方針：元の三つの射影への回収式と三出力の実 dg 関手の結合則を使う。
規約：元の対象・全 Hom を保持。使われ方：Rivera–Zeinalian Prop.4.6 の結合則。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の三重直積から実三重 dg tensor への oplax tensor は結合関手と両立する。 -/
lemma cubicalLambdaOplaxTensor_associativity (K L N : SSet.{u}) :
    DGFunctor.comp
        (DGFunctor.comp (cubicalLambdaOplaxTensor A (K ⨯ L) N)
          (dgTensorFunctor A (cubicalLambdaOplaxTensor A K L)
            (DGFunctor.id (CubicalLambda A N))))
        (dgTensorAssociator A (CubicalLambda A K) (CubicalLambda A L) (CubicalLambda A N)) =
      DGFunctor.comp
        (DGFunctor.comp (cubicalLambdaMap A (Limits.prod.associator K L N).hom)
          (cubicalLambdaOplaxTensor A K (L ⨯ N)))
        (dgTensorFunctor A (DGFunctor.id (CubicalLambda A K))
          (cubicalLambdaOplaxTensor A L N)) := by
  let S := (K ⨯ L) ⨯ N
  let R := K ⨯ (L ⨯ N)
  let a : S ⟶ K := prod.fst ≫ prod.fst
  let b : S ⟶ L := prod.fst ≫ prod.snd
  let c : S ⟶ N := prod.snd
  let ar : R ⟶ K := prod.fst
  let br : R ⟶ L := prod.snd ≫ prod.fst
  let cr : R ⟶ N := prod.snd ≫ prod.snd
  let h : S ⟶ R := (Limits.prod.associator K L N).hom
  have hl := cubicalLambdaTensorPair_split_left A
    (prod.fst : S ⟶ K ⨯ L) (prod.snd : S ⟶ N)
    (prod.fst : K ⨯ L ⟶ K) (prod.snd : K ⨯ L ⟶ L)
  have hla := congrArg (fun F => DGFunctor.comp F
    (dgTensorAssociator A (CubicalLambda A K) (CubicalLambda A L) (CubicalLambda A N))) hl
  have hri := cubicalLambdaTensorPair_split_right A
    (prod.fst : R ⟶ K) (prod.snd : R ⟶ L ⨯ N)
    (prod.fst : L ⨯ N ⟶ L) (prod.snd : L ⨯ N ⟶ N)
  have hr := (enrichedFunctor_comp_assoc
    (cubicalLambdaMap A h) (cubicalLambdaOplaxTensor A K (L ⨯ N))
    (dgTensorFunctor A (DGFunctor.id (CubicalLambda A K))
      (cubicalLambdaOplaxTensor A L N))).trans
    ((congrArg (fun F => DGFunctor.comp (cubicalLambdaMap A h) F) hri).trans
      (cubicalLambdaTripleRight_precompose A h ar br cr))
  have hf : h ≫ ar = a := by simp [h, ar, a]
  have hg : h ≫ br = b := by simp [h, br, b]
  have hh : h ≫ cr = c := by simp [h, cr, c]
  have ht := (congrArg (fun f => cubicalLambdaTripleRight A f (h ≫ br) (h ≫ cr)) hf).trans
    ((congrArg (fun g => cubicalLambdaTripleRight A a g (h ≫ cr)) hg).trans
      (congrArg (fun k => cubicalLambdaTripleRight A a b k) hh))
  exact hla.trans ((cubicalLambdaTriplePair_associativity A a b c).trans (hr.trans ht).symm)

end SerrePositivity.KST.SConstruction
