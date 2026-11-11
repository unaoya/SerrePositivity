module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingRoofFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofWeakEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.WeakHomotopyDescent

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 二つの屋根比較に沿って、任意標的の固定 Hom へ降下する実写像とホモトピー。 -/
structure DGInvertingHomDescent (P : Set D) (x y : D) {Y : SSet.{max u v}}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) where
  evaluation : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoof A D P x F (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))
  evaluation_homotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap A D P x F
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) ≫ evaluation) (𝟙 _)
  extension : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondence A D P x y ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))
  extension_homotopy : SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y ≫ extension)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F ≫ evaluation)

/-- 任意の反転関手には、実屋根比較に沿う写像空間上の降下が存在する。 -/
theorem dgInvertingHomDescent_nonempty (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (x y : D) {Y : SSet.{max u v}} [Quasicategory Y] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)) :
    Nonempty (DGInvertingHomDescent A D P x y F) := by
  obtain ⟨r, ⟨Hr⟩⟩ :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap_isWeakHomotopyEquivalence A D P x F hF
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))).homotopyExtension (𝟙 _)
  obtain ⟨q, ⟨Hq⟩⟩ :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap_isWeakHomotopyEquivalence A D P hP x y).homotopyExtension
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F ≫ r)
  exact ⟨⟨r, Hr, q, Hq⟩⟩

/-- 屋根上の降下から得る、商の実 Hom 全体に定義された写像。 -/
def DGInvertingHomDescent.homMap (P : Set D) (x y : D) {Y : SSet.{max u v}}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y) (C : DGInvertingHomDescent A D P x y F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (DGQuotient.QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj x) ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y ≫ C.extension

/-- 商の Hom への延長は、元の Hom 上で任意関手の実際の作用とホモトピック。 -/
theorem DGInvertingHomDescent.homMap_restriction (P : Set D) (x y : D)
    {Y : SSet.{max u v}} [Quasicategory Y] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
    (C : DGInvertingHomDescent A D P x y F) :
    Nonempty (SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((DGQuotient.inclusion A D P).map x y) ≫
        DGInvertingHomDescent.homMap A D P x y F C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mp
  have h₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr
    ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp C.extension_homotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOriginalFixedHomRoofMap A D P x y)⟩
  change SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_ ≫ (_ ≫ C.extension))) =
    SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_ ≫ (_ ≫ C.evaluation))) at h₁
  simp only [← Category.assoc] at h₁
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFixedHomRoofMap_comparison, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap_fixedHom] at h₁
  have h₂ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr
    ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp C.evaluation_homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))⟩
  simp only [Category.assoc, Category.comp_id] at h₁ h₂
  exact h₁.trans h₂

/-- 写像空間上の延長は、二つの屋根降下の選択によらずホモトピック。 -/
theorem DGInvertingHomDescent.homMap_unique (P : Set D) (hP : _root_.SerrePositivity.DifferentialGraded.DGQuotient.localKFlat A D P)
    (x y : D) {Y : SSet.{max u v}} [Quasicategory Y] (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P))
    (C C' : DGInvertingHomDescent A D P x y F) :
    Nonempty (SSet.Homotopy (DGInvertingHomDescent.homMap A D P x y F C)
      (DGInvertingHomDescent.homMap A D P x y F C')) := by
  obtain ⟨H⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.weakRoofDescent_unique
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap_isWeakHomotopyEquivalence A D P hP x y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFixedHomRoofMap_isWeakHomotopyEquivalence A D P x F hF
      (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingRoofFunctorMap A D P x y F) C.evaluation C'.evaluation C.extension C'.extension
    C.evaluation_homotopy C'.evaluation_homotopy C.extension_homotopy C'.extension_homotopy
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientFixedHomRoofMap A D P x y)⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
