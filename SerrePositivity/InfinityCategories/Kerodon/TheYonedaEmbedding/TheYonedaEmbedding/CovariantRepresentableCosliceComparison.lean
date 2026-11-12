module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ReversedRepresentableValueFactorization
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CovariantRepresentableValueNormalization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CovariantCosliceFiberNormalization

/-!
概要：元の共変表現可能値の比較を、同じ coslice の右写像空間比較へ全族で接続する。
方針：元の反転 Hom 比較の厳密な分解と指定逆の相殺を使う。
規約：正本の値比較・逆・左右比較の選択を保持する。
使われ方：G8 の表現可能値の標準後合成との自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions MorphismSpaces IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：元の coslice の右写像空間比較は、指定左 pinched 比較と左右比較の合成。
方針：定義を展開し、指定同型の逆と順射を相殺する。
規約：順射の厳密な等式。使われ方：正本の表現可能値への接続。 -/
lemma cosliceRightMapping_hom_factor {C : SSet.{u}} [Quasicategory C] (x y : C _⦋0⦌) :
    (cosliceFiberRightMappingEquivalence x y).hom =
      (cosliceFiberPinchedLeftIso x y).hom ≫ (pinchedHomLeftRightEquivalence x y).hom := by
  simp only [cosliceFiberRightMappingEquivalence, pinchedHomLeftRightEquivalence,
    pinchedHomLeftToIntervalMappingSpace, QCatEquivalence.trans, QCatEquivalence.symm,
    IsQCatEquivalence.choose, Category.assoc, Iso.hom_inv_id_assoc]

/-- 概要：元の共変表現可能値の比較は、同じ反転 coslice の値比較の上で元の右 Hom 比較に同型。
方針：反転 Hom の比較を厳密に分解し、元の指定逆と反転 fiber の標準同型を相殺する。
規約：全写像間の同型。使われ方：元の表現可能値の比較に自然性を渡す。 -/
def covariantRepresentableValue_cosliceIso {C : SSet.{u}} [Quasicategory C]
    (x y : C _⦋0⦌) :
    FunctorIso
      ((reversedRepresentableValueEquivalence (B := C.op) (SSet.opObjEquiv.symm x)
        (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm y))).hom ≫
          (covariantRepresentableValueEquivalence x y).hom)
      (pointCosliceFiberMap (SSet.opFunctorCompOpFunctorIso.app C).hom
        (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm x))
        (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm y)) ≫
          (cosliceFiberRightMappingEquivalence x y).hom) := by
  let a := representablePresheafOppositeHomValueEquivalence (C := C.op)
    (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)
  let k := (SSet.opFunctor.mapIso (pinchedHomSliceFiberIso (X := C.op)
    (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x))) ≪≫
      pointSliceReverseFiberIso (B := C.op) (SSet.opObjEquiv.symm x) (SSet.opObjEquiv.symm y)
  let v := reversedRepresentableValueEquivalence (B := C.op) (SSet.opObjEquiv.symm x)
    (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm y))
  let f := covariantRepresentableValueEquivalence x y
  let l := pinchedHomLeftRightEquivalence x y
  let K := pointCosliceFiberMap (SSet.opFunctorCompOpFunctorIso.app C).hom
    (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm x))
    (SSet.opObjEquiv.symm (SSet.opObjEquiv.symm y))
  let R := (cosliceFiberRightMappingEquivalence x y).hom
  have hk : (pinchedHomSliceFiberIso (X := C.op) (SSet.opObjEquiv.symm y)
      (SSet.opObjEquiv.symm x)).hom =
      pinchedHomToSliceFiber (X := C.op) (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x) := rfl
  have ha : a.hom = k.hom ≫ v.hom := by
    simpa only [a, k, v, Iso.trans_hom, Functor.mapIso_hom, hk, Category.assoc] using
      representableOppositeHomValue_hom_factor (B := C.op)
        (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)
  have hl : FunctorIso (a.hom ≫ f.hom) l.hom := by
    have h := FunctorIso.precomp (covariantRepresentableValueNormalizationIso x y) a.hom
    have h' := FunctorIso.postcomp a.homInvIso l.hom
    simp only [Category.assoc, Category.id_comp] at h h'
    exact h ≪≫ h'
  have hr : k.hom ≫ K ≫ R = l.hom := by
    change covariantCosliceFiberNormalization x y ≫ R = l.hom
    rw [covariantCosliceFiberNormalization_eq_inv]
    dsimp only [R, l]
    rw [cosliceRightMapping_hom_factor]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hL : k.hom ≫ (v.hom ≫ f.hom) = a.hom ≫ f.hom := by
    rw [← Category.assoc, ← ha]
  have hR : k.hom ≫ (K ≫ R) = l.hom := hr
  have hp : FunctorIso (k.hom ≫ (v.hom ≫ f.hom)) (k.hom ≫ (K ≫ R)) := by
    rw [hL, hR]
    exact hl
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using FunctorIso.precomp hp k.inv

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
