module
public import SerrePositivity.InfinityCategories.Derived.DGInvertingRoofFunctor
public import SerrePositivity.InfinityCategories.Derived.DGActualRoofWeakEquivalence
public import SerrePositivity.InfinityCategories.Derived.WeakHomotopyDescent

/-! # 反転関手の商の実写像空間への延長

概要：任意の反転関手の実 Hom 上の作用を、商の実 Hom 全体へ延長する。
方針：反転関手の屋根の固定 Hom 包含と、実商屋根比較の二つの弱同値に沿って降下する。
規約：写像空間の各対についての構成。合成・単位との coherent な両立はまだ主張しない。
使われ方：局所化の関手圏比較の写像空間上の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 二つの屋根比較に沿って、任意標的の固定 Hom へ降下する実写像とホモトピー。 -/
structure DGInvertingHomDescent (P : Set D) (x y : D) {Y : SSet.{max u v}}
    (F : dgNerve A D ⟶ Y) where
  evaluation : dgInvertingRoof A D P x F (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)) ⟶
    pinchedHom (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x))
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y))
  evaluation_homotopy : SSet.Homotopy
    (dgInvertingFixedHomRoofMap A D P x F
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)) ≫ evaluation) (𝟙 _)
  extension : dgQuotientRoofCorrespondence A D P x y ⟶
    pinchedHom (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x))
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y))
  extension_homotopy : SSet.Homotopy (dgRoofCorrespondenceMap A D P x y ≫ extension)
    (dgInvertingRoofFunctorMap A D P x y F ≫ evaluation)

/-- 任意の反転関手には、実屋根比較に沿う写像空間上の降下が存在する。 -/
theorem dgInvertingHomDescent_nonempty (P : Set D) (hP : DGQuotient.localKFlat A D P)
    (x y : D) {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (hF : InvertsEdges F (dgVerdierEdges A D P)) :
    Nonempty (DGInvertingHomDescent A D P x y F) := by
  obtain ⟨r, ⟨Hr⟩⟩ :=
    (dgInvertingFixedHomRoofMap_isWeakHomotopyEquivalence A D P x F hF
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y))).homotopyExtension (𝟙 _)
  obtain ⟨q, ⟨Hq⟩⟩ :=
    (dgRoofCorrespondenceMap_isWeakHomotopyEquivalence A D P hP x y).homotopyExtension
      (dgInvertingRoofFunctorMap A D P x y F ≫ r)
  exact ⟨⟨r, Hr, q, Hq⟩⟩

/-- 屋根上の降下から得る、商の実 Hom 全体に定義された写像。 -/
def DGInvertingHomDescent.homMap (P : Set D) (x y : D) {Y : SSet.{max u v}}
    (F : dgNerve A D ⟶ Y) (C : DGInvertingHomDescent A D P x y F) :
    DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj x) ((DGQuotient.inclusion A D P).obj y) ⟶
    pinchedHom (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x))
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)) :=
  dgQuotientFixedHomRoofMap A D P x y ≫ C.extension

/-- 商の Hom への延長は、元の Hom 上で任意関手の実際の作用とホモトピック。 -/
theorem DGInvertingHomDescent.homMap_restriction (P : Set D) (x y : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (C : DGInvertingHomDescent A D P x y F) :
    Nonempty (SSet.Homotopy
      (pinchedHomChainMap ((DGQuotient.inclusion A D P).map x y) ≫
        DGInvertingHomDescent.homMap A D P x y F C)
      (pinchedHomMap F (Simplex.vertex x) (Simplex.vertex y))) := by
  apply (functorVertex_piZero_eq_iff_homotopy _ _).mp
  have h₁ := (functorVertex_piZero_eq_iff_homotopy _ _).mpr
    ⟨functorHomotopyPrecomp C.extension_homotopy (dgOriginalFixedHomRoofMap A D P x y)⟩
  change SSet.π₀.mk (functorVertex (_ ≫ (_ ≫ C.extension))) =
    SSet.π₀.mk (functorVertex (_ ≫ (_ ≫ C.evaluation))) at h₁
  simp only [← Category.assoc] at h₁
  rw [dgFixedHomRoofMap_comparison, dgInvertingRoofFunctorMap_fixedHom] at h₁
  have h₂ := (functorVertex_piZero_eq_iff_homotopy _ _).mpr
    ⟨functorHomotopyPrecomp C.evaluation_homotopy
      (pinchedHomMap F (Simplex.vertex x) (Simplex.vertex y))⟩
  simp only [Category.assoc, Category.comp_id] at h₁ h₂
  exact h₁.trans h₂

/-- 写像空間上の延長は、二つの屋根降下の選択によらずホモトピック。 -/
theorem DGInvertingHomDescent.homMap_unique (P : Set D) (hP : DGQuotient.localKFlat A D P)
    (x y : D) {Y : SSet.{max u v}} [Quasicategory Y] (F : dgNerve A D ⟶ Y)
    (hF : InvertsEdges F (dgVerdierEdges A D P))
    (C C' : DGInvertingHomDescent A D P x y F) :
    Nonempty (SSet.Homotopy (DGInvertingHomDescent.homMap A D P x y F C)
      (DGInvertingHomDescent.homMap A D P x y F C')) := by
  obtain ⟨H⟩ := weakRoofDescent_unique
    (dgRoofCorrespondenceMap_isWeakHomotopyEquivalence A D P hP x y)
    (dgInvertingFixedHomRoofMap_isWeakHomotopyEquivalence A D P x F hF
      (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y)))
    (dgInvertingRoofFunctorMap A D P x y F) C.evaluation C'.evaluation C.extension C'.extension
    C.evaluation_homotopy C'.evaluation_homotopy C.extension_homotopy C'.extension_homotopy
  exact ⟨functorHomotopyPrecomp H (dgQuotientFixedHomRoofMap A D P x y)⟩

end SerrePositivity.InfinityCategories
