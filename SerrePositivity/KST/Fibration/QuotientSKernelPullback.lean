module
public import SerrePositivity.KST.Fibration.RelativeSKernelRealizationPullback
public import SerrePositivity.KST.Fibration.RelativeSQuotientRealization
public import SerrePositivity.KST.Comparison.ExInfinityHomotopyPullback

/-! # 商実現比較を入力した、元の S• 包含・商射・零合成を保つ核四角形 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)

/-- 元の相対 S の零合成の全単体を、同じ商の core S へ送った四角形。 -/
theorem quotientSKernelSquare :
    CommSq (relativeSimplicialSConstructionCoreInclusion (i.hom ≫ q.hom))
      (coreSExactMap i)
      (relativeSimplicialFunctorMap i q.hom ≫ relativeSimplicialQuotientMap q)
      (coreSExactMap q) := by
  constructor
  rw [← Category.assoc, (relativeSimplicialKernelSquare i q.hom).w,
    Category.assoc, relativeSimplicialQuotientMap_core]

/-- 全単体の零合成を保った商核四角形を、四つの実対象と元の射のまま実現する。 -/
theorem quotientSKernelRealizationSquare :
    CommSq (simplicialDiagonalFunctor.map
      (relativeSimplicialSConstructionCoreInclusion (i.hom ≫ q.hom)))
      (simplicialDiagonalFunctor.map (coreSExactMap i))
      (simplicialDiagonalFunctor.map
        (relativeSimplicialFunctorMap i q.hom ≫ relativeSimplicialQuotientMap q))
      (simplicialDiagonalFunctor.map (coreSExactMap q)) :=
  simplicialDiagonalFunctor.map_commSq (quotientSKernelSquare i q)

/-- 同じ商実現比較が可逆なら、元の商核四角形そのものが homotopy pullback。 -/
theorem quotientSKernelRealizationSquare_homotopyPullback
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (hq : IsIso (AnodyneHomotopy.anodyneQ.map
      (simplicialDiagonalFunctor.map (relativeSimplicialQuotientMap q)))) :
    IsHomotopyPullback (quotientSKernelRealizationSquare i q) := by
  apply (isHomotopyPullback_iff_of_localized_isIso
    (relativeSKernelRealizationSquare i q) (quotientSKernelRealizationSquare i q)
    (𝟙 _) (𝟙 _) (𝟙 _)
    (simplicialDiagonalFunctor.map (relativeSimplicialQuotientMap q))
    ?_ ?_ ?_ ?_ (by infer_instance) (by infer_instance) (by infer_instance) hq).mp
  · exact relativeSKernelRealizationSquare_homotopyPullback h
  · simp only [Category.comp_id, Category.id_comp]
  · simp only [Category.comp_id, Category.id_comp]
  · simp only [Category.id_comp]
    exact (simplicialDiagonalFunctor.map_comp _ _).symm
  · simpa only [Category.id_comp] using relativeSQuotientRealization_core q

/-- 同じ元の四角形は、Ex∞ による四頂点の Kan 化の後にも homotopy pullback。 -/
theorem quotientSKernelRealizationSquare_exInfinity_homotopyPullback
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (hq : IsIso (AnodyneHomotopy.anodyneQ.map
      (simplicialDiagonalFunctor.map (relativeSimplicialQuotientMap q)))) :
    IsHomotopyPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_commSq (quotientSKernelRealizationSquare i q)) :=
  (isHomotopyPullback_exInfinity_iff _).mpr
    (quotientSKernelRealizationSquare_homotopyPullback i q h hq)

/-- 元の段ごとの商比較を入力すれば、元の商核四角形は同じ射のまま引き戻しとなる。 -/
theorem quotientSKernelRealizationSquare_homotopyPullback_of_stages
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (hq : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map (relativeSQuotientMap q n))) :
    IsHomotopyPullback (quotientSKernelRealizationSquare i q) :=
  quotientSKernelRealizationSquare_homotopyPullback i q h
    (relativeSQuotientRealization_localized_isIso_of_stages q hq)

end SerrePositivity.KST.Fibration
