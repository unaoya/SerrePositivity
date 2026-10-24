module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaFiniteSubsetKanValues
public import SerrePositivity.InfinityCategories.F2.Presentable.PointKanExtension

/-!
概要：P_Σ 内の表現可能対象の任意の小余積は Ind(C) に属する。
方針：有限部分集合上の表現可能な左 Kan 値の filtered 余極限として表示する。
規約：元の指定余積余錐と前層への包含を保持する。
使われ方：反映した bar 図式の各次数の Ind 条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：表現可能対象の元の小余積の前層像は Ind_aleph0 に属する。
方針：元の有限部分集合の次数射影に沿う左 Kan 延長を filtered に実現する。
規約：Ind 側の交換定理を新たな入力にしない。
使われ方：simplicial Ind 表示の各項の構成。 -/
lemma sigmaYoneda_smallCoproduct_isInd {C : SSet.{u}} [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    {I : Type u} (p : nerve (Discrete I) ⟶ C)
    (c : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map p ≫ sigmaYonedaInfinityMap C))
    (hc : IsColimitCone c) :
    Ind.IsIndVertex Cardinal.aleph0 C
      ((sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌) c.vertex) := by
  let Y := finiteSubsetFamily I
  let δ := nerveMap (Functor.Elements.π Y)
  let q := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (finiteSubsetForget I))
  obtain ⟨G, β, hβ⟩ := sigmaSmallRepresentable_exists_leftKanExtension hC δ
    (nerveMap (finiteSubsetForget I) ≫ p)
  obtain ⟨d, hd⟩ := sigma_hasSmallSiftedColimits C (nerve (Finset I)) G
  have hfiltered : IsKappaFiltered Cardinal.aleph0 (nerve (Finset I)) :=
    (isKappaFiltered_aleph0_iff _).mpr inferInstance
  have hind : Ind.IsIndVertex Cardinal.aleph0 C
      ((sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌) d.vertex) := by
    have hh := Ind.isIndVertex_kappaColimitClosed Cardinal.aleph0 C (nerve (Finset I))
      (G ≫ sigmaPresheafInfinityInclusion C)
      (mapJoinCocone (sigmaPresheafInfinityInclusion C) d)
      (sigmaInclusion_map_isColimit G d hd) (fun b ↦ ?_)
    · rwa [Ind.mapJoinCocone_vertex] at hh
    · obtain ⟨s, rfl⟩ := nerveEquiv.symm.surjective b
      obtain ⟨x, ⟨e⟩⟩ := sigmaFiniteSubsetKan_value_representable hC p β hβ s
      have ey : (sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌)
          ((sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up x)) =
          (yonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up x) :=
        congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (ULift.up x))
          (sigmaYonedaInfinityMap_inclusion C)
      let e' := VertexIso.map e (sigmaPresheafInfinityInclusion C) ≪≫
        eqToIso (congrArg HomotopyCategory.mk ey)
      exact Ind.isIndVertex_isoClosed Cardinal.aleph0 C e'.symm
        (Ind.isIndVertex_yoneda Cardinal.aleph0 x)
  have hqc := (Ind.isColimitCone_iff_restrict_rightCofinal q
    (Ind.isRightCofinal_ulift _ (finiteSubsetForget_nerve_isRightCofinal I)) c).mp hc
  have he : q ≫ ((SSet.uliftFunctor.{u + 1, u}).map p ≫ sigmaYonedaInfinityMap C) =
      (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (finiteSubsetForget I) ≫ p) ≫
        sigmaYonedaInfinityMap C := by
    simp only [q, Functor.map_comp, Category.assoc]
  let c' : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (finiteSubsetForget I) ≫ p) ≫ sigmaYonedaInfinityMap C) :=
    ⟨(c.restrict q).val, (c.restrict q).property.trans he⟩
  have hc' := (F2.isColimitCone_iff_of_cocone_val_eq (c.restrict q) c' rfl).mp hqc
  let e := leftKan_colimitVertexIso ((SSet.uliftFunctor.{u + 1, u}).map δ) β hβ c' hc' d hd
  exact Ind.isIndVertex_isoClosed Cardinal.aleph0 C
    (VertexIso.map e (sigmaPresheafInfinityInclusion C)) hind

end SerrePositivity.InfinityCategories.F2.Presentable
