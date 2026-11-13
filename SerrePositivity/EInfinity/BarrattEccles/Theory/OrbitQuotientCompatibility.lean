module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.BinaryInputActionEquality

/-!
# 固定 arity の軌道直和と指定包含

HA 3.2.4.7 の自由比較の始域側。BS-W16 の型一覧 L04 に対応する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory HomologicalComplex Limits
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
attribute [local instance] Classical.propDecidable
variable (R : Type u) [CommRing R] (X Y : Complex R)

set_option maxHeartbeats 800000 in
-- 軌道表示と Schur 表示の複体を同時に照合するため計算上限を広げる。
/-- 各標準代表の指定包含は、軌道直和の同じ指定商と包含へ送られる。 -/
lemma schurArityOrbitIso_word_quotient (r : ℕ) (k : ULift.{u} (Fin (r + 1))) :
    ((operad R).arity r ◁
      binaryTensorWordInclusion X Y r (binaryTensorCountPattern r k.down)) ≫
    arityCoinvariantComplexQuotient (schurDiagram R (sequence R) (X ⊞ Y)) r ≫
      (schurArityOrbitIso X Y r).hom =
    (β_ ((operad R).arity r)
      (binaryTensorWordObj X Y r (binaryTensorCountPattern r k.down))).hom ≫
    coinvariantTotalQuotient
      (binaryTensorWordFixedAction X Y r (binaryTensorCountPattern r k.down)
        ((MulEquiv.ulift : ULift.{u} (Equiv.Perm (Fin r)) ≃*
          Equiv.Perm (Fin r)).toMonoidHom.comp (binaryTensorPatternSubgroup r k).subtype)
        (fun g => g.property))
      ((arityComplexAction R r).comp (binaryTensorPatternSubgroup r k).subtype) ≫
      Sigma.ι (orbitCoefficientComplex X Y r) k := by
  let T := inputCoinvariantTotalFunctor (arityRepresentationCochain R r)
  apply (cancel_mono ((schurArityOrbitIso X Y r).inv ≫
    (schurArityInputCoefficientIso R (X ⊞ Y) r).hom ≫
    (T.mapIso (binaryTensorFullInputSequenceIso R X Y r)).hom)).1
  dsimp only [T]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simp only [schurArityOrbitIso, Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc,
    inputCoinvariantTotalCoproductIso, PreservesCoproduct.inv_hom,
    Sigma.ι_mapIso_inv_assoc, ι_comp_sigmaComparison_assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Functor.mapIso_inv, Iso.symm_inv]
  rw [← Functor.map_comp, binaryTensorOrbitComplexIso_ι]
  rw [reassoc_of% (schurArityInputCoefficientIso_quotient R (X ⊞ Y) r)]
  simp only [Functor.mapIso_hom, binaryTensorFullInputSequenceIso]
  erw [coinvariantTotalQuotient_transport_left
    (finiteBijectionComplexAction (bijectionFunctor (X ⊞ Y)) r)
    (binaryTensorPowerAction X Y r MulEquiv.ulift.toMonoidHom)
    (arityComplexAction R r) (binaryTensorInputAction_eq R X Y r)]
  have hb := BraidedCategory.braiding_naturality (𝟙 ((operad R).arity r))
    (binaryTensorWordInclusion X Y r (binaryTensorCountPattern r k.down))
  simp only [tensorHom_def, id_whiskerRight, whiskerLeft_id,
    Category.id_comp, Category.comp_id] at hb
  rw [reassoc_of% hb]
  apply congrArg (fun f => (β_ ((operad R).arity r)
    (binaryTensorWordObj X Y r (binaryTensorCountPattern r k.down))).hom ≫ f)
  apply HomologicalComplex.Hom.ext
  funext l
  apply mapBifunctor.hom_ext
  intro i j h
  change ιMapBifunctor (binaryTensorWordObj X Y r (binaryTensorCountPattern r k.down))
    ((operad R).arity r) (curriedTensor (ModuleCat R)) (.up ℤ) i j l h ≫
    (mapBifunctorMap (binaryTensorWordInclusion X Y r (binaryTensorCountPattern r k.down))
      (𝟙 ((operad R).arity r)) (curriedTensor (ModuleCat R)) (.up ℤ) ≫
      coinvariantTotalQuotient (binaryTensorPowerAction X Y r MulEquiv.ulift.toMonoidHom)
        (arityComplexAction R r)).f l = _
  rw [HomologicalComplex.comp_f, ι_mapBifunctorMap_assoc, coinvariantTotalQuotient_ι]
  rw [HomologicalComplex.comp_f, reassoc_of% coinvariantTotalQuotient_ι]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact (inducedCoinvariantTotalIso_inv_inclusion (binaryTensorPatternSubgroup r k)
    (binaryTensorOrbitInput X Y r k) (binaryTensorFullInput X Y r)
    (arityRepresentationCochain R r) (binaryTensorOrbitInputInclusion X Y r k)
    i j l h x y).symm

end SerrePositivity.EInfinity.BarrattEccles
