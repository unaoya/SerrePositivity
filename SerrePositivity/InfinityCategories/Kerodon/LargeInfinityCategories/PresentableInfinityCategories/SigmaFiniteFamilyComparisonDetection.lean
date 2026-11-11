module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.DiscreteFamilyUpdateVertices
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.DiscreteFamilyUpdatePreservation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FilteredGeometricFunctorOperations

/-!
概要：有限離散図式上の全比較の可逆性を、全成分が Yoneda 像である図式で検出する。
方針：一成分更新関手と元の P_Σ の生成による検出を有限座標で反復する。
規約：全ての工程で同じ指定比較射を使う。
使われ方：元の Yoneda 制限上の有限余積保存から全有限余積保存へ移す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

local instance {I : Type u} : DecidableEq I := Classical.decEq I

/-- 概要：指定した有限座標集合の外では元の Yoneda 像である図式。
方針：元の離散成分の実際の頂点を量化する。
規約：元の小さい底と元の Yoneda を使う。
使われ方：座標帰納法の仮定。 -/
def IsSigmaYonedaFamilyOutside {I : Type u} (C : SSet.{u}) [Quasicategory C] (S : Finset I)
    (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) : Prop :=
  ∀ j, j ∉ S → ∃ x, p.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk j))) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) x

/-- 概要：Yoneda 像での検出を一つの任意の成分へ広げる。
方針：一成分更新で指定比較を制限し、元の filtered・実現生成で可逆性を検出する。
規約：他の成分の元の全図式を保持する。
使われ方：有限座標の帰納法の一段。 -/
lemma sigmaFamilyComparison_extend_coordinate
    {I : Type u} {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p)
    {F G : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)))).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C)) ⟶ D}
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits Cardinal.aleph0 F)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits Cardinal.aleph0 G)
    (hFg : _root_.SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.PreservesSmallGeometricRealizations F) (hGg : _root_.SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.PreservesSmallGeometricRealizations G)
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) (S : Finset I)
    (hS : ∀ p, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsSigmaYonedaFamilyOutside C S p →
      IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p))) (i : I)
    (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsSigmaYonedaFamilyOutside C (insert i S) p) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) := by
  classical
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteFamilyUpdate p i
  let θ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (a ≫ F) (a ≫ G) := (hoFunctor.map ((pre a).app D)).toFunctor.map η
  have ha := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteFamilyUpdate_preservesSmallSiftedColimits p i
  have hθ : IsIso θ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.sigmaComparison_isIso_of_filtered_geometric hC
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservesSmallFilteredColimits_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.preservesSmallFiltered_of_sifted ha) hF)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservesSmallFilteredColimits_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.preservesSmallFiltered_of_sifted ha) hG)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservesSmallGeometricRealizations_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.preservesSmallGeometric_of_sifted ha) hFg)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservesSmallGeometricRealizations_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.preservesSmallGeometric_of_sifted ha) hGg) θ
    intro x
    let q := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteFamilyUpdatedDiagram p i ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C).app _ x)
    have hq : IsSigmaYonedaFamilyOutside C S q := by
      intro j hj
      change ∃ y, (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteFamilyUpdatedDiagram p i _).app _ _ = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteFamilyUpdatedDiagram_evaluate]
      by_cases hji : j = i
      · rw [ite_eq_left hji]
        exact ⟨x, rfl⟩
      · rw [ite_eq_right hji]
        exact hp j (by simp only [Finset.mem_insert, not_or]; exact ⟨hji, hj⟩)
    have h := hS q hq
    have he := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_precomp η a ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C).app _ x)
    change _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate θ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C).app _ x) = _ at he
    have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteFamilyUpdatedDiagram_vertex p i ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C).app _ x)
    have hi : IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteFamilyUpdate p i).app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C).app _ x))) :=
      (congrArg (fun v ↦ IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η v)) hv).mp h
    exact he.symm ▸ hi
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_isIso θ
    (p.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk i))))
  have he := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_precomp η a
    (p.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk i))))
  change _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate θ _ = _ at he
  have hi : IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η (a.app (Opposite.op ⦋0⦌)
      (p.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk i)))))) := he ▸ h
  have hv : a.app (Opposite.op ⦋0⦌)
      (p.app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk i)))) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteFamilyUpdatedDiagram_vertex p i _).symm.trans
      (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.discreteFamilyUpdatedDiagram_original p i))
  exact (congrArg (fun v ↦ IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η v)) hv).mp hi

/-- 概要：有限離散図式上の比較は全成分が Yoneda 像のときにだけ検査すればよい。
方針：各成分で元の filtered・実現生成を有限回使う。
規約：指定全比較自身を可逆とする。
使われ方：Yoneda 制限上の有限余積保存による全余極限保存判定。 -/
lemma sigmaFiniteFamilyComparison_isIso
    {I : Type u} [Finite I] {C : SSet.{u}} [Quasicategory C]
    {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p)
    {F G : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)))).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C)) ⟶ D}
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits Cardinal.aleph0 F)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits Cardinal.aleph0 G)
    (hFg : _root_.SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.PreservesSmallGeometricRealizations F) (hGg : _root_.SerrePositivity.InfinityCategories.Kerodon.ExactnessAndAnimation.SimplicialObjectsOfInfinityCategories.PreservesSmallGeometricRealizations G)
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G)
    (hη : ∀ p, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsSigmaYonedaFamilyOutside C ∅ p →
      IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p))) : IsIso η := by
  classical
  let := Fintype.ofFinite I
  have hS (S : Finset I) : ∀ p, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsSigmaYonedaFamilyOutside C S p →
      IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate η (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)) := by
    induction S using Finset.induction_on with
    | empty => exact hη
    | @insert i S _ ih =>
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaFamilyComparison_extend_coordinate hC hF hG hFg hGg η S ih i
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHom_isIso_of_components
  intro v
  obtain ⟨p, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).surjective v
  exact hS Finset.univ p (fun j hj ↦ False.elim (hj (Finset.mem_univ j)))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
