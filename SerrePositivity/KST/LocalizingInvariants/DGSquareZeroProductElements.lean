module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroProjection
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
概要：平方零代数の四つの積成分を、元の斉次元上で計算する。
方針：実代数の四成分の等式を純 tensor で評価する。
規約：単位・積は元の実 chain map。使われ方：cone の追加微分の Leibniz 則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] (A : Mon (Complex R)) (M : Bimod A A)

lemma mul_ll_apply (p q n : ℤ) (hn : p + q = n) (a : A.X.X p) (b : A.X.X q) :
    μ[(algebra A M).X].f n (ιTensorObj (algebra A M).X (algebra A M).X p q n hn
      ((biprod.inl : A.X ⟶ (algebra A M).X).f p a ⊗ₜ[R]
        (biprod.inl : A.X ⟶ (algebra A M).X).f q b)) =
    (biprod.inl : A.X ⟶ (algebra A M).X).f n
      (μ[A.X].f n (ιTensorObj A.X A.X p q n hn (a ⊗ₜ[R] b))) := by
  have h := congrArg (fun k => k.f n (ιTensorObj A.X A.X p q n hn (a ⊗ₜ[R] b)))
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.mul_ll A M)
  change μ[(algebra A M).X].f n ((biprod.inl ⊗ₘ biprod.inl : A.X ⊗ A.X ⟶
    (algebra A M).X ⊗ (algebra A M).X).f n
    (ιTensorObj A.X A.X p q n hn (a ⊗ₜ[R] b))) = _ at h
  exact (congrArg (fun z => μ[(algebra A M).X].f n z)
    (tensorMap_apply biprod.inl biprod.inl p q n hn a b)).symm.trans h

lemma mul_lr_apply (p q n : ℤ) (hn : p + q = n) (a : A.X.X p) (m : M.X.X q) :
    μ[(algebra A M).X].f n (ιTensorObj (algebra A M).X (algebra A M).X p q n hn
      ((biprod.inl : A.X ⟶ (algebra A M).X).f p a ⊗ₜ[R]
        (biprod.inr : M.X ⟶ (algebra A M).X).f q m)) =
    (biprod.inr : M.X ⟶ (algebra A M).X).f n
      (M.actLeft.f n (ιTensorObj A.X M.X p q n hn (a ⊗ₜ[R] m))) := by
  have h := congrArg (fun k => k.f n (ιTensorObj A.X M.X p q n hn (a ⊗ₜ[R] m)))
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.mul_lr A M)
  change μ[(algebra A M).X].f n ((biprod.inl ⊗ₘ biprod.inr : A.X ⊗ M.X ⟶
    (algebra A M).X ⊗ (algebra A M).X).f n
    (ιTensorObj A.X M.X p q n hn (a ⊗ₜ[R] m))) = _ at h
  exact (congrArg (fun z => μ[(algebra A M).X].f n z)
    (tensorMap_apply biprod.inl biprod.inr p q n hn a m)).symm.trans h

lemma mul_rl_apply (p q n : ℤ) (hn : p + q = n) (m : M.X.X p) (a : A.X.X q) :
    μ[(algebra A M).X].f n (ιTensorObj (algebra A M).X (algebra A M).X p q n hn
      ((biprod.inr : M.X ⟶ (algebra A M).X).f p m ⊗ₜ[R]
        (biprod.inl : A.X ⟶ (algebra A M).X).f q a)) =
    (biprod.inr : M.X ⟶ (algebra A M).X).f n
      (M.actRight.f n (ιTensorObj M.X A.X p q n hn (m ⊗ₜ[R] a))) := by
  have h := congrArg (fun k => k.f n (ιTensorObj M.X A.X p q n hn (m ⊗ₜ[R] a)))
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.mul_rl A M)
  change μ[(algebra A M).X].f n ((biprod.inr ⊗ₘ biprod.inl : M.X ⊗ A.X ⟶
    (algebra A M).X ⊗ (algebra A M).X).f n
    (ιTensorObj M.X A.X p q n hn (m ⊗ₜ[R] a))) = _ at h
  exact (congrArg (fun z => μ[(algebra A M).X].f n z)
    (tensorMap_apply biprod.inr biprod.inl p q n hn m a)).symm.trans h

lemma mul_rr_apply (p q n : ℤ) (hn : p + q = n) (m : M.X.X p) (m' : M.X.X q) :
    μ[(algebra A M).X].f n (ιTensorObj (algebra A M).X (algebra A M).X p q n hn
      ((biprod.inr : M.X ⟶ (algebra A M).X).f p m ⊗ₜ[R]
        (biprod.inr : M.X ⟶ (algebra A M).X).f q m')) = 0 := by
  have h := congrArg (fun k => k.f n (ιTensorObj M.X M.X p q n hn (m ⊗ₜ[R] m')))
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.mul_rr A M)
  change μ[(algebra A M).X].f n ((biprod.inr ⊗ₘ biprod.inr : M.X ⊗ M.X ⟶
    (algebra A M).X ⊗ (algebra A M).X).f n
    (ιTensorObj M.X M.X p q n hn (m ⊗ₜ[R] m'))) = 0 at h
  exact (congrArg (fun z => μ[(algebra A M).X].f n z)
    (tensorMap_apply biprod.inr biprod.inr p q n hn m m')).symm.trans h

end SerrePositivity.KST.LocalizingInvariants.SquareZero
