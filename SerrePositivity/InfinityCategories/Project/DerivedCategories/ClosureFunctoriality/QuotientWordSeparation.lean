module
public import SerrePositivity.DifferentialGraded.Quotient.Path.Construction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.TensorDegreeSeparation

/-!
概要：Drinfeld 商の内部 path 直和で、指定した有限語の成分を読み取る。
方針：同じ余積の普遍性から次数別分裂と異なる語の分離を得る。
規約：最終商の微分に関する複体射とは主張しない。商 Hom 作用は構成しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory Limits MonoidalCategory HomologicalComplex DifferentialGraded
open DGQuotient
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (S : Set D) (x y : D)

/-- 内部直和から指定した語の項だけを読む。 -/
def dgQuotientWordProjection (w : Word S) :
    internalHom R D S x y ⟶ term R D w x y := by
  classical
  exact Sigma.desc (fun v => if h : v = w then eqToHom (by rw [h]) else 0)

lemma dgQuotientWordProjection_split (w : Word S) :
    ι R D S x y w ≫ dgQuotientWordProjection R D S x y w = 𝟙 _ := by
  classical
  unfold ι dgQuotientWordProjection
  rw [Sigma.ι_desc]
  simp

lemma dgQuotientWordProjection_other (w v : Word S) (h : v ≠ w) :
    ι R D S x y v ≫ dgQuotientWordProjection R D S x y w = 0 := by
  classical
  unfold ι dgQuotientWordProjection
  rw [Sigma.ι_desc]
  simp [h]

/-- 内部 path 直和の次数別普遍性。複体射でない成分族も貼り合わせる。 -/
def dgQuotientDegreeDesc (n : ℤ) (M : ModuleCat R)
    (f : ∀ w : Word S, (term R D w x y).X n ⟶ M) :
    (internalHom R D S x y).X n ⟶ M :=
  (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat R) (.up ℤ) n)
    (colimit.isColimit (Discrete.functor (fun w : Word S => term R D w x y)))).desc
    { pt := M
      ι := Discrete.natTrans (fun w => f w.as) }

lemma dgQuotientDegreeDesc_ι (n : ℤ) (M : ModuleCat R)
    (f : ∀ w : Word S, (term R D w x y).X n ⟶ M) (w : Word S) :
    (ι R D S x y w).f n ≫ dgQuotientDegreeDesc R D S x y n M f = f w :=
  (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat R) (.up ℤ) n)
    (colimit.isColimit (Discrete.functor (fun w : Word S => term R D w x y)))).fac _
      (Discrete.mk w)

/-- 内部 path 直和の次数別射は、同じ各語上の値で決まる。 -/
lemma dgQuotientDegreeHom_ext (n : ℤ) (M : ModuleCat R)
    (f g : (internalHom R D S x y).X n ⟶ M)
    (h : ∀ w : Word S, (ι R D S x y w).f n ≫ f = (ι R D S x y w).f n ≫ g) :
    f = g :=
  (isColimitOfPreserves (HomologicalComplex.eval (ModuleCat R) (.up ℤ) n)
    (colimit.isColimit (Discrete.functor (fun w : Word S => term R D w x y)))).hom_ext
      (fun w => h w.as)

/-- 指定語の包含は全ての次数で単射。 -/
lemma dgQuotientWordInclusion_injective (w : Word S) (n : ℤ) :
    Function.Injective ((ι R D S x y w).f n) := by
  intro a b hab
  have ha := ConcreteCategory.congr_hom
    (congrArg (fun f => f.f n) (dgQuotientWordProjection_split R D S x y w)) a
  have hb := ConcreteCategory.congr_hom
    (congrArg (fun f => f.f n) (dgQuotientWordProjection_split R D S x y w)) b
  change (dgQuotientWordProjection R D S x y w).f n ((ι R D S x y w).f n a) = a at ha
  change (dgQuotientWordProjection R D S x y w).f n ((ι R D S x y w).f n b) = b at hb
  exact ha.symm.trans ((congrArg ((dgQuotientWordProjection R D S x y w).f n) hab).trans hb)

/-- 異なる収縮語の同じ全次数での等号は、指定語の係数を零にする。 -/
lemma dgQuotientWord_separation (w v : Word S) (h : v ≠ w) (n : ℤ)
    (a : (term R D w x y).X n) (b : (term R D v x y).X n)
    (hab : (ι R D S x y w).f n a = (ι R D S x y v).f n b) : a = 0 := by
  have ha := ConcreteCategory.congr_hom
    (congrArg (fun f => f.f n) (dgQuotientWordProjection_split R D S x y w)) a
  have hb := ConcreteCategory.congr_hom
    (congrArg (fun f => f.f n) (dgQuotientWordProjection_other R D S x y w v h)) b
  change (dgQuotientWordProjection R D S x y w).f n ((ι R D S x y w).f n a) = a at ha
  change (dgQuotientWordProjection R D S x y w).f n ((ι R D S x y v).f n b) = 0 at hb
  exact ha.symm.trans ((congrArg ((dgQuotientWordProjection R D S x y w).f n) hab).trans hb)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
