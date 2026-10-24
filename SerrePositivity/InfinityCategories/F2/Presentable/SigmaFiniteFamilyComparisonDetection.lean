module

public import SerrePositivity.InfinityCategories.F2.Presentable.DiscreteFamilyUpdateVertices
public import SerrePositivity.InfinityCategories.F2.Presentable.DiscreteFamilyUpdatePreservation
public import SerrePositivity.InfinityCategories.F2.Presentable.FilteredGeometricFunctorOperations

/-!
概要：有限離散図式上の全比較の可逆性を、全成分が Yoneda 像である図式で検出する。
方針：一成分更新関手と元の P_Σ の生成による検出を有限座標で反復する。
規約：全ての工程で同じ指定比較射を使う。
使われ方：元の Yoneda 制限上の有限余積保存から全有限余積保存へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind
local instance {I : Type u} : DecidableEq I := Classical.decEq I

/-- 概要：指定した有限座標集合の外では元の Yoneda 像である図式。
方針：元の離散成分の実際の頂点を量化する。
規約：元の小さい底と元の Yoneda を使う。
使われ方：座標帰納法の仮定。 -/
def IsSigmaYonedaFamilyOutside {I : Type u} (C : SSet.{u}) [Quasicategory C] (S : Finset I)
    (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶
      SigmaPresheafInfinity C) : Prop :=
  ∀ j, j ∉ S → ∃ x, p.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Discrete.mk j))) =
    (sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) x

/-- 概要：Yoneda 像での検出を一つの任意の成分へ広げる。
方針：一成分更新で指定比較を制限し、元の filtered・実現生成で可逆性を検出する。
規約：他の成分の元の全図式を保持する。
使われ方：有限座標の帰納法の一段。 -/
lemma sigmaFamilyComparison_extend_coordinate
    {I : Type u} {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    {F G : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)))).obj
      (SigmaPresheafInfinity C)) ⟶ D}
    (hF : PreservesSmallKappaFilteredColimits Cardinal.aleph0 F)
    (hG : PreservesSmallKappaFilteredColimits Cardinal.aleph0 G)
    (hFg : PreservesSmallGeometricRealizations F) (hGg : PreservesSmallGeometricRealizations G)
    (η : FunctorHom F G) (S : Finset I)
    (hS : ∀ p, IsSigmaYonedaFamilyOutside C S p →
      IsIso (functorHomEvaluate η (functorVertex p))) (i : I)
    (p : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ SigmaPresheafInfinity C)
    (hp : IsSigmaYonedaFamilyOutside C (insert i S) p) :
    IsIso (functorHomEvaluate η (functorVertex p)) := by
  classical
  let a := discreteFamilyUpdate p i
  let θ : FunctorHom (a ≫ F) (a ≫ G) := (hoFunctor.map ((pre a).app D)).toFunctor.map η
  have ha := discreteFamilyUpdate_preservesSmallSiftedColimits p i
  have hθ : IsIso θ := by
    apply sigmaComparison_isIso_of_filtered_geometric hC
      (preservesSmallFilteredColimits_comp (preservesSmallFiltered_of_sifted ha) hF)
      (preservesSmallFilteredColimits_comp (preservesSmallFiltered_of_sifted ha) hG)
      (preservesSmallGeometricRealizations_comp (preservesSmallGeometric_of_sifted ha) hFg)
      (preservesSmallGeometricRealizations_comp (preservesSmallGeometric_of_sifted ha) hGg) θ
    intro x
    let q := discreteFamilyUpdatedDiagram p i ((sigmaYonedaInfinityMap C).app _ x)
    have hq : IsSigmaYonedaFamilyOutside C S q := by
      intro j hj
      change ∃ y, (discreteFamilyUpdatedDiagram p i _).app _ _ = _
      rw [discreteFamilyUpdatedDiagram_evaluate]
      by_cases hji : j = i
      · rw [ite_eq_left hji]
        exact ⟨x, rfl⟩
      · rw [ite_eq_right hji]
        exact hp j (by simp only [Finset.mem_insert, not_or]; exact ⟨hji, hj⟩)
    have h := hS q hq
    have he := functorHomEvaluate_precomp η a ((sigmaYonedaInfinityMap C).app _ x)
    change functorHomEvaluate θ ((sigmaYonedaInfinityMap C).app _ x) = _ at he
    have hv := discreteFamilyUpdatedDiagram_vertex p i ((sigmaYonedaInfinityMap C).app _ x)
    have hi : IsIso (functorHomEvaluate η
        ((discreteFamilyUpdate p i).app _ ((sigmaYonedaInfinityMap C).app _ x))) :=
      (congrArg (fun v ↦ IsIso (functorHomEvaluate η v)) hv).mp h
    exact he.symm ▸ hi
  have h := functorHomEvaluate_isIso θ
    (p.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Discrete.mk i))))
  have he := functorHomEvaluate_precomp η a
    (p.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Discrete.mk i))))
  change functorHomEvaluate θ _ = _ at he
  have hi : IsIso (functorHomEvaluate η (a.app (Opposite.op ⦋0⦌)
      (p.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Discrete.mk i)))))) := he ▸ h
  have hv : a.app (Opposite.op ⦋0⦌)
      (p.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Discrete.mk i)))) = functorVertex p :=
    (discreteFamilyUpdatedDiagram_vertex p i _).symm.trans
      (congrArg functorVertex (discreteFamilyUpdatedDiagram_original p i))
  exact (congrArg (fun v ↦ IsIso (functorHomEvaluate η v)) hv).mp hi

/-- 概要：有限離散図式上の比較は全成分が Yoneda 像のときにだけ検査すればよい。
方針：各成分で元の filtered・実現生成を有限回使う。
規約：指定全比較自身を可逆とする。
使われ方：Yoneda 制限上の有限余積保存による全余極限保存判定。 -/
lemma sigmaFiniteFamilyComparison_isIso
    {I : Type u} [Finite I] {C : SSet.{u}} [Quasicategory C]
    {D : SSet.{u + 1}} [Quasicategory D]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    {F G : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)))).obj
      (SigmaPresheafInfinity C)) ⟶ D}
    (hF : PreservesSmallKappaFilteredColimits Cardinal.aleph0 F)
    (hG : PreservesSmallKappaFilteredColimits Cardinal.aleph0 G)
    (hFg : PreservesSmallGeometricRealizations F) (hGg : PreservesSmallGeometricRealizations G)
    (η : FunctorHom F G)
    (hη : ∀ p, IsSigmaYonedaFamilyOutside C ∅ p →
      IsIso (functorHomEvaluate η (functorVertex p))) : IsIso η := by
  classical
  let := Fintype.ofFinite I
  have hS (S : Finset I) : ∀ p, IsSigmaYonedaFamilyOutside C S p →
      IsIso (functorHomEvaluate η (functorVertex p)) := by
    induction S using Finset.induction_on with
    | empty => exact hη
    | @insert i S _ ih =>
        exact sigmaFamilyComparison_extend_coordinate hC hF hG hFg hGg η S ih i
  apply F1B.kanFunctorHom_isIso_of_components
  intro v
  obtain ⟨p, rfl⟩ := (functorVertexEquiv _ _).surjective v
  exact hS Finset.univ p (fun j hj ↦ False.elim (hj (Finset.mem_univ j)))

end SerrePositivity.InfinityCategories.F2.Presentable
