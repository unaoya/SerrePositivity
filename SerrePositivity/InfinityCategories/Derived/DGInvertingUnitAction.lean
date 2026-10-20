module
public import SerrePositivity.InfinityCategories.Derived.DGInvertingBinaryAction
public import SerrePositivity.InfinityCategories.Derived.DGFunctorPinchedIdentity
public import SerrePositivity.InfinityCategories.Derived.FunctorRestrictionFamilyIso
/-!
概要：商 Hom の全降下選択空間上の作用が、実恒等族を保つことを証明する。
方針：元の Hom への全体制限同型を実恒等族で評価し、任意の選択パラメータで展開する。
規約：元の実恒等一次単体と任意パラメータを保つ。使われ方：局所化延長の単位整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]
variable (P : Set D) (x : D) {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
/-- 実恒等族における作用は、全降下選択空間上で標的の同じ実恒等族に同型。 -/
def dgInvertingUnitActionIso (K : SSet.{max u v}) :
    FunctorIso (dgInvertingHomActionFamily A D P x x F ≫
      (pre (SSet.const (X := K) (pinchedIdentityVertex (X := dgQuotientNerve A D P)
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj x))))).app _)
      (SSet.const (functorVertex (SSet.const (X := K)
        (pinchedIdentityVertex (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x)))))) := by
  apply functorRestrictionFamilyIso_of_eq
    (dgInvertingHomActionFamily A D P x x F)
    (pinchedHomChainMap ((DGQuotient.inclusion A D P).map x x))
    (pinchedHomMap F (Simplex.vertex x) (Simplex.vertex x))
    (dgInvertingHomActionFamilyRestrictionIso A D P x x F)
    (SSet.const (X := K) (pinchedIdentityVertex (X := dgNerve A D) (Simplex.vertex x)))
  · exact (SSet.const_comp _ _).trans (congrArg (fun a => SSet.const (X := K) a)
      (dgFunctorPinchedMap_identityVertex (DGQuotient.inclusion A D P) x))
  · exact (SSet.const_comp _ _).trans (congrArg (fun a => SSet.const (X := K) a)
      (pinchedHomMap_identityVertex F (Simplex.vertex x)))
/-- 任意の全選択パラメータ上で、実恒等族の作用は同じ関手圏の恒等射を表す。 -/
lemma dgInvertingUnitAction_id (K S : SSet.{max u v})
    (p : S ⟶ dgInvertingHomDescentSpace A D P x x F) :
    intervalFamilyHom (dgInvertingHomFamilyValue A D P x x F
      (SSet.const (X := K) (pinchedIdentityVertex (X := dgQuotientNerve A D P)
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj x)))) p ≫
          pinchedHomToIntervalMappingSpace _ _) = 𝟙 _ := by
  let g := SSet.const (X := K)
    (pinchedIdentityVertex (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x)))
  let H := functorFamilyIsoUncurry_const g (dgInvertingUnitActionIso A D P x F K) p
  have h : Nonempty (SSet.Homotopy
      (dgInvertingHomFamilyValue A D P x x F
        (SSet.const (X := K) (pinchedIdentityVertex (X := dgQuotientNerve A D P)
          (Simplex.vertex ((DGQuotient.inclusion A D P).obj x)))) p)
      (SSet.const (X := K ⊗ S)
        (pinchedIdentityVertex (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x))))) :=
    ⟨stableHomotopyRetarget H rfl (SSet.comp_const _ _)⟩
  exact ((pinchedFamilyHom_eq_iff_homotopy).mpr h).trans
    (pinchedFamilyHom_identity (K := K ⊗ S) (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x)))
end SerrePositivity.InfinityCategories
