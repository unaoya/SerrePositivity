module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgPiZeroForget
public import SerrePositivity.EInfinity.BarrattEccles.ZeroDegreeHomologyProduct
public import SerrePositivity.EInfinity.BarrattEccles.CAlgDiscreteDerivedComparison

/-!
# 離散入力の π₀

## 概要
Berger–Fresse §1 の H⁰ を離散可換代数で計算する。

## 方針
閉零次の代表を評価し、既存の零入力と二入力の比較で積と単位を読む。

## 規約
通常の代数の射と構造写像も保つ。

## 使われ方
BS 著者版 Theorem 6.2 の `pi0_discrete` 欄。
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex DifferentialGraded SSet _root_.SerrePositivity.HomologyZero
open SerrePositivity.InfinityCategories

variable {A : Type u} [CommRing A]

private abbrev M (B : CommAlgCat.{u} A) := ModuleCat.of A B
private abbrev X (B : CommAlgCat.{u} A) := (discreteAlgebraFunctor A).obj B

private def discreteHomologyLinearEquiv (B : CommAlgCat.{u} A) :
    (X B).carrier.homology 0 ≃ₗ[A] B :=
  (_root_.SerrePositivity.HomologyZero.componentHomologyLinearEquiv (cochainSingleZero (M B))).symm.trans
    (singleObjXSelf (.up ℤ) 0 (M B)).toLinearEquiv

private lemma discreteHomologyLinearEquiv_class (B : CommAlgCat.{u} A)
    (f : 𝟙_ (Complex A) ⟶ (X B).carrier) :
    discreteHomologyLinearEquiv B (_root_.SerrePositivity.HomologyZero.unitClass (X B).carrier f) = _root_.SerrePositivity.HomologyZero.singleValue (M B) f := by
  let K := cochainSingleZero (M B)
  change (singleObjXSelf (.up ℤ) 0 (M B)).hom
    ((_root_.SerrePositivity.HomologyZero.componentHomologyLinearEquiv K).symm (_root_.SerrePositivity.HomologyZero.unitClass K f)) =
      (singleObjXSelf (.up ℤ) 0 (M B)).hom (cycleFromUnit K f).val
  rw [← _root_.SerrePositivity.HomologyZero.componentHomologyLinearEquiv_unit, LinearEquiv.symm_apply_apply]

private lemma discreteHomologyLinearEquiv_one (B : CommAlgCat.{u} A) :
    discreteHomologyLinearEquiv B (homologyOne (X B)) = 1 := by
  rw [homologyOne, discreteHomologyLinearEquiv_class, homologyNullary_discrete]
  change _root_.SerrePositivity.HomologyZero.singleValue (M B) ((CochainComplex.singleFunctor (ModuleCat A) 0).map
    (ModuleCat.ofHom (Algebra.linearMap A B))) = 1
  rw [← Category.id_comp ((CochainComplex.singleFunctor (ModuleCat A) 0).map _), _root_.SerrePositivity.HomologyZero.singleValue_map]
  exact map_one (algebraMap A B)

private lemma discreteHomologyLinearEquiv_mul (B : CommAlgCat.{u} A)
    (x y : (X B).carrier.homology 0) :
    discreteHomologyLinearEquiv B (_root_.SerrePositivity.HomologyZero.pairingValue (homologyBinary (X B)) x y) =
      discreteHomologyLinearEquiv B x * discreteHomologyLinearEquiv B y := by
  obtain ⟨f, rfl⟩ := _root_.SerrePositivity.HomologyZero.unitClass_surjective (X B).carrier x
  obtain ⟨g, rfl⟩ := _root_.SerrePositivity.HomologyZero.unitClass_surjective (X B).carrier y
  simp only [_root_.SerrePositivity.HomologyZero.pairingValue_class, discreteHomologyLinearEquiv_class, homologyBinary_discrete]
  change _root_.SerrePositivity.HomologyZero.singleValue (M B) (_root_.SerrePositivity.HomologyZero.unitPairing ((cochainSingleTensorIso _ _).hom ≫
    (CochainComplex.singleFunctor (ModuleCat A) 0).map
      (ModuleCat.ofHom (LinearMap.mul' A B))) f g) = _
  exact _root_.SerrePositivity.HomologyZero.singlePairing_value (M B) (M B) (M B)
    (ModuleCat.ofHom (LinearMap.mul' A B)) f g

private def discreteHomologyAlgebraEquiv (B : CommAlgCat.{u} A) :
    homologyCommAlgebra (X B) ≃ₐ[A] B :=
  { discreteHomologyLinearEquiv B with
    map_mul' := discreteHomologyLinearEquiv_mul B
    commutes' := fun r => by
      change discreteHomologyLinearEquiv B (r • homologyOne (X B)) = algebraMap A B r
      rw [map_smul, discreteHomologyLinearEquiv_one, Algebra.algebraMap_eq_smul_one] }

/-- The usual H⁰ of a discrete algebra recovers the original algebra functorially. -/
@[no_expose]
def discreteHomologyAlgebraIso (A : Type u) [CommRing A] :
    discreteAlgebraFunctor A ⋙ homologyAlgebraFunctor A ≅ 𝟭 (CommAlgCat.{u} A) := by
  refine NatIso.ofComponents (fun B => CommAlgCat.isoMk (discreteHomologyAlgebraEquiv B)) ?_
  intro B D g
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨f, rfl⟩ := _root_.SerrePositivity.HomologyZero.unitClass_surjective (X B).carrier x
  change discreteHomologyLinearEquiv D
    (homologyMap ((discreteAlgebraFunctor A).map g).hom 0 (_root_.SerrePositivity.HomologyZero.unitClass (X B).carrier f)) =
      g.hom (discreteHomologyLinearEquiv B (_root_.SerrePositivity.HomologyZero.unitClass (X B).carrier f))
  rw [_root_.SerrePositivity.EInfinity.HomologyZero.unitClass_naturality, discreteHomologyLinearEquiv_class,
    discreteHomologyLinearEquiv_class, discreteAlgebraFunctor_map, _root_.SerrePositivity.HomologyZero.singleValue_map]
  rfl

set_option maxHeartbeats 900000 in
-- Check the composite through the ordinary source and the equivalence with the undercategory.
/-- 離散代数の埋め込み上の π₀ は恒等関手と自然同型。 -/
def barrattEcclesPi0_discrete (A : Type u) [CommRing A] :
    ordinaryToHoNerve (RingAlgebra A) ⋙ hoMap (discreteCAlgUnderEmbedding A) ⋙
      barrattEcclesPi0 A ≅ 𝟭 (RingAlgebra A) := by
  let E := commAlgCatEquivUnder (CommRingCat.of A)
  let F := E.inverse ⋙ discreteAlgebraFunctor A
  let Q := algebraCAlgSource A
  let P := barrattEcclesPi0 A
  have h : discreteCAlgUnderEmbedding A = nerveMap F ≫ Q := rfl
  rw [h]
  calc
    _ ≅ F ⋙ ordinaryAlgebraHoSource A ⋙ P := by
      simpa only [Functor.assoc, ordinaryAlgebraHoSource, Q, P] using
        (Functor.isoWhiskerLeft (ordinaryToHoNerve (RingAlgebra A))
          (Functor.isoWhiskerRight (hoMapCompIso (nerveMap F) Q) P) ≪≫
          (by simpa only [Functor.assoc] using
            Functor.isoWhiskerRight (ordinaryToHoNerve_naturalIso F) (hoMap Q ⋙ P)))
    _ ≅ F ⋙ strictPiZero A :=
      Functor.isoWhiskerLeft F (barrattEcclesPi0_sourceIso A)
    _ ≅ E.inverse ⋙ E.functor := by
      simpa only [Functor.assoc, Functor.id_comp, F, strictPiZero] using
        Functor.isoWhiskerLeft E.inverse
          (Functor.isoWhiskerRight (discreteHomologyAlgebraIso A) E.functor)
    _ ≅ _ := E.counitIso

end SerrePositivity.EInfinity.BarrattEccles
