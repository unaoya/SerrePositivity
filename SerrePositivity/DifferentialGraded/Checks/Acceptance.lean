module
public import SerrePositivity.DifferentialGraded.Category.Examples
public import SerrePositivity.DifferentialGraded.Category.Components
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Data.ZMod.Basic

/-! # U0–U3 の受入例

任意可換環、次数 0/−1/1、標数二、準同値の二条件を検証する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits ZeroObject MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

example : DGCategory A (Complex A) := inferInstance
example : DGCategory A PUnit.{1} := inferInstance
example : EnrichedOrdinaryCategory (Complex A) (Complex A) := inferInstance
example : Category (HomotopyCategory A (Complex A)) := inferInstance
example : Linear A (HomotopyCategory A (Complex A)) := inferInstance
example : (DGFunctor.id (A := A) (Complex A)).onHomotopy.Linear A := inferInstance
example : QuasiEquivalence (DGFunctor.id (A := A) (Complex A)) := quasiEquivalence_id

example (X Y Z : Complex A) (f : Homogeneous X Y 0) (g : Homogeneous Y Z 0) :
    (enrichedComposition X Y Z).f 0
      (ιTensorObj (homComplex A X Y) (homComplex A Y Z) 0 0 0 rfl (f ⊗ₜ[A] g)) =
      f.comp g rfl := by simpa using enrichedComposition_apply X Y Z 0 0 0 rfl f g

example (X Y Z : Complex A) (f : Homogeneous X Y (-1)) (g : Homogeneous Y Z 1) :
    (enrichedComposition X Y Z).f 0
      (ιTensorObj (homComplex A X Y) (homComplex A Y Z) (-1) 1 0 (by omega) (f ⊗ₜ[A] g)) =
      -(f.comp g (by omega)) := by
  simpa using enrichedComposition_apply X Y Z (-1) 1 0 (by omega) f g

example (X Y Z : Complex A) (f : Homogeneous X Y 1) (g : Homogeneous Y Z 1) :
    (enrichedComposition X Y Z).f 2
      (ιTensorObj (homComplex A X Y) (homComplex A Y Z) 1 1 2 rfl (f ⊗ₜ[A] g)) =
      -(f.comp g rfl) := by simpa using enrichedComposition_apply X Y Z 1 1 2 rfl f g

example : DGCategory (ZMod 2) (Complex (ZMod 2)) := inferInstance
example (X : Complex (ZMod 2)) (h : Homogeneous X X (-1))
    (dh : δ (-1) 0 h = Cochain.ofHom (𝟙 X)) : Homotopy (𝟙 X) 0 :=
  contractingHomotopy X h dh

/-- 空の dg 圏。Hom 条件と本質的全射を混同しないための受入例。 -/
instance emptyEnrichment : DGCategory A Empty where
  Hom x := nomatch x
  id x := nomatch x
  comp x := nomatch x
  id_comp x := nomatch x
  comp_id x := nomatch x
  assoc x := nomatch x

/-- 空圏から一対象 A への唯一の dg 関手。 -/
def emptyToRing : DGFunctor A Empty PUnit.{1} where
  obj x := nomatch x
  map x := nomatch x
  map_id x := nomatch x
  map_comp x := nomatch x

/-- Hom 準同型条件だけなら空圏からの関手も満たす。 -/
lemma emptyToRing_homQuasiIso : HomQuasiIso (emptyToRing A) := fun x => nomatch x

/-- Hom 準同型条件から H⁰ の本質的全射は従わない。 -/
lemma emptyToRing_not_essSurj : ¬ (emptyToRing A).onHomotopy.EssSurj := by
  intro h
  have he := h.mem_essImage
    ((toHomotopy A PUnit.{1}).obj (ForgetEnrichment.of (Complex A) PUnit.unit))
  obtain ⟨x, _⟩ := he
  exact Empty.elim (ForgetEnrichment.to (Complex A) x.as)
/-- 零 dg 圏の対象型。環の一対象例とは instance を分離する。 -/
def ZeroObjects := ULift.{0, 0} PUnit.{1}

/-- 零 dg 圏の対象は一つ。 -/
instance : Unique ZeroObjects := inferInstanceAs (Unique (ULift.{0, 0} PUnit.{1}))

/-- 零複体を Hom とする一対象 dg 圏。 -/
instance zeroEnrichment : DGCategory A ZeroObjects where
  Hom _ _ := 0
  id _ := 0
  comp _ _ _ := 0
  id_comp _ _ := (isZero_zero (Complex A)).eq_of_tgt _ _
  comp_id _ _ := (isZero_zero (Complex A)).eq_of_tgt _ _
  assoc _ _ _ _ := (isZero_zero (Complex A)).eq_of_tgt _ _

/-- 閉次数零圏でも対象は一つ。 -/
instance : Unique (ClosedCategory A ZeroObjects) := inferInstanceAs (Unique ZeroObjects)

/-- 一対象 A から零 dg 圏への関手。 -/
def ringToZero : DGFunctor A PUnit.{1} ZeroObjects where
  obj _ := default
  map _ _ := 0
  map_id _ := (isZero_zero (Complex A)).eq_of_tgt _ _
  map_comp _ _ _ := (isZero_zero (Complex A)).eq_of_tgt _ _

/-- 対象が一つなので H⁰ の本質的全射条件を満たす。 -/
lemma ringToZero_essSurj : (ringToZero A).onHomotopy.EssSurj where
  mem_essImage _y :=
    ⟨(toHomotopy A PUnit.{1}).obj (ForgetEnrichment.of (Complex A) PUnit.unit),
      ⟨eqToIso (Subsingleton.elim _ _)⟩⟩

/-- 非零環では Hom 準同型条件を満たさない。本質的全射だけから準同値は得られない。 -/
lemma ringToZero_not_homQuasiIso [Nontrivial A] : ¬ HomQuasiIso (ringToZero A) := by
  intro h
  have := h PUnit.unit PUnit.unit
  have hz : (0 : Complex A).ExactAt 0 := ExactAt.of_isZero
    ((eval (ModuleCat A) (.up ℤ) 0).map_isZero (Limits.isZero_zero (Complex A)))
  have hs : IsZero ((𝟙_ (Complex A)).homology 0) :=
    IsZero.of_iso hz.isZero_homology
      (isoOfQuasiIsoAt ((ringToZero A).map PUnit.unit PUnit.unit) 0)
  have hA : IsZero (𝟙_ (ModuleCat A)) :=
    IsZero.of_iso hs (singleObjHomologySelfIso (.up ℤ) 0 (𝟙_ (ModuleCat A))).symm
  have := ModuleCat.subsingleton_of_isZero hA
  exact one_ne_zero (Subsingleton.elim (1 : A) 0)
end SerrePositivity.DifferentialGraded.Checks
