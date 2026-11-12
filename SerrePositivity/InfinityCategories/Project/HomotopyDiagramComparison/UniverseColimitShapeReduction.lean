module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeValEquality

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeShapePrecomposition
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseCoconeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerAnodyneReplacement
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.InnerAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.TrivialFibrationCocone

/-!
概要：前層などの宇宙変更の小余極限保存を、quasicategory 添字だけの検証から戻す。
方針：元の小さい添字を inner anodyne に置換し、全余錐を延長して保存・反映する。
規約：元の指定全余錐を厳密な制限で保持。元の添字の充填性・sifted 性は不要。
使われ方：任意の小さい sifted 添字に対する P_Σ 延長の保存性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 小さい quasicategory 添字での保存は、任意の小さい添字での同じ全余錐像の保存を与える。 -/
lemma mapUliftCocone_isColimit_of_quasicategoryShapes
    {X : SSet.{u + 1}} {Y : SSet.{u + 2}}
    [Quasicategory X] [Quasicategory Y]
    (q : (SSet.uliftFunctor.{u + 2, u + 1}).obj X ⟶ Y)
    (h : ∀ (J : SSet.{u}) [Quasicategory J]
      (D : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶ X) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u + 1, u + 2} c)))
    {I : SSet.{u}} (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ X)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone q (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u + 1, u + 2} c)) := by
  let f : I ⟶ (Δ[0] : SSet.{u}) :=
    SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))
  obtain ⟨J, i, p, hi, hJ, hp, hfac⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.exists_quasicategory_resolution_over f
  have : Quasicategory J := hJ
  let i₁ := (SSet.uliftFunctor.{u + 1, u}).map i
  have hi₁ : innerAnodyneExtensions i₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.innerAnodyneExtensions_ulift_map i hi
  have : Mono i₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.mono_of_innerAnodyne _ hi₁
  have he₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_innerAnodyne i₁ hi₁
  obtain ⟨d, e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_coconeExtension_of_mono_precomposition i₁ he₁ c
  have hec : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone e := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_mono_precomposition i₁ he₁ e).mpr
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ he).mpr hc)
  have hqe := h J d e hec
  let i₂ := (SSet.uliftFunctor.{u + 2, u + 1}).map i₁
  have hi₂ : innerAnodyneExtensions i₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.innerAnodyneExtensions_ulift_map i₁ hi₁
  have : Mono i₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.mono_of_innerAnodyne _ hi₂
  have hreq := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_mono_precomposition i₂
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_innerAnodyne i₂ hi₂) _).mp hqe
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ ?_).mp hreq
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i₂ (𝟙 _) ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u + 1, u + 2} e).val ≫ q) = _
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ulift_restrictJoinCocone_val]
  change ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso _ 0).inv ≫
    (SSet.uliftFunctor.{u + 2, u + 1}).map (e.restrict i₁).val) ≫ q = _
  rw [he]
  rfl
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
