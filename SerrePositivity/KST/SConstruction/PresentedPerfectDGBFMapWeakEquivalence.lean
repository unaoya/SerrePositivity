module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFOrdinaryNaturality
public import SerrePositivity.KST.SConstruction.PointedWeakComparisonSquare
public import SerrePositivity.KST.Spectra.SpectrumHomotopyEquivalences
public import SerrePositivity.KST.Spectra.PostMappingIsomorphism

/-! # 元の境界 Kan 射の弱同値から同じ実 BF 射への移送
概要：元の全境界 Kan 射が全基点 π 同型なら、同じ実 BF 射も全段で π 同型。
方針：零段は loop、正段は前向き弱比較の厳密自然性を用いて移す。
規約：境界射の条件は明示する。使われ方：新 BF 関手の Morita 不変性の判定。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ Ex∞ 境界値の Kan 性を比較四角形の型でも保持する。 -/
local instance presentedPerfectDGBFMapBoundary_kanComplex
    (r : ℕ) (X : PerfDGInput.{u, v} A) :
    KanComplex (((presentedPerfectDGBFBoundaryFunctor A r).obj X).obj).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _

/-- 元の全境界 Kan 射の全基点 π 同型性は、同じ実 BF 射の全段へ移る。 -/
lemma presentedPerfectDGBFMap_levelwise_of_boundary
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y)
    (hf : ∀ r, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (presentedPerfectDGBoundaryKanMap A r f).hom.right)
    (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((presentedPerfectDGBFMap A f).app n).right := by
  cases n with
  | zero =>
      rw [presentedPerfectDGBFMap_zero_app]
      exact PointedMapping.post_piIsomorphism PointedSimplicialSet.circle _ (hf 0)
  | succ r =>
      let S := presentedPerfectDGBFPositiveStage A r
      let : KanComplex (S.functor.obj X).obj.right := S.kan X
      let : KanComplex (S.functor.obj Y).obj.right := S.kan Y
      let c : ((presentedPerfectDGBFBoundaryFunctor A r).obj X).obj ⟶
          (S.functor.obj X).obj := S.comparison X
      let d : ((presentedPerfectDGBFBoundaryFunctor A r).obj Y).obj ⟶
          (S.functor.obj Y).obj := S.comparison Y
      have hc : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism c.right :=
        kanPiIsomorphism_of_localized_isIso _ (S.weak X)
      have hd : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism d.right :=
        kanPiIsomorphism_of_localized_isIso _ (S.weak Y)
      have h := pointedPiIsomorphism_of_weakComparisonSquare
        (presentedPerfectDGBoundaryKanMap A r f).hom c d
        (show (S.functor.obj X).obj ⟶ (S.functor.obj Y).obj from
          _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryMap S.functor f) (hf r) hc hd
        (presentedPerfectDGBFStageComparison_naturality A r S f)
      erw [presentedPerfectDGBFMap_positive_app A f r]
      exact h

/-- 元の全境界 Kan 射の弱同値性は、同じ実 BF 射の全整数 π 同型性を与える。 -/
lemma presentedPerfectDGBFMap_piIsomorphism_of_boundary
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y)
    (hf : ∀ r, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (presentedPerfectDGBoundaryKanMap A r f).hom.right) :
    OmegaSpectrum.PiIsomorphism (presentedPerfectDGBFMap A f) :=
  OmegaSpectrum.piIsomorphism_of_levelwise _
    (presentedPerfectDGBFMap_levelwise_of_boundary A f hf)

end SerrePositivity.KST.SConstruction
