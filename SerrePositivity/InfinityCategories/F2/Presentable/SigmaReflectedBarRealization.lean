module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaReflectedBarDegree
public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafBarRealization

/-!
概要：全前層の元の bar に専用反映を適用した simplicial Ind 実現。
方針：同じ幾何学的実現を左随伴で保存し、可逆余単位で元の P_Σ 対象へ戻す。
規約：元の bar・反映・全余錐を保持する。
使われ方：P_Σ の filtered 余極限と幾何学的実現による生成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind

/-- 概要：元の前層 bar の反映は、各項が Ind に属し、元の P_Σ 対象を実現する。
方針：元の実現の保存と反映の同じ可逆余単位を合成する。
規約：別の単体的図式へ置き換えず、構成済みの bar と L の合成を使う。
使われ方：採用した専用反映経路による simplicial Ind 表示。 -/
lemma sigmaReflector_bar_realization {C : SSet.{u}} [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
    {L : PresheafInfinity C ⟶ SigmaPresheafInfinity C}
    (β : SSet.Homotopy (sigmaYonedaInfinityMap C) (yonedaInfinityMap C ≫ L))
    (hβ : IsLeftKanExtension (yonedaInfinityMap C) (sigmaYonedaInfinityMap C) L β)
    (v : (SigmaPresheafInfinity C) _⦋0⦌) :
    ∃ d : JoinCocone (presheafBarObject (sigmaPresheafVertexFunctor v) ≫ L),
      IsColimitCone d ∧ Nonempty (VertexIso d.vertex v) ∧
      ∀ n : SmallSimplexOpposite.{u}, IsIndVertex Cardinal.aleph0 C
        ((sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌)
          ((presheafBarObject (sigmaPresheafVertexFunctor v) ≫ L).app
            (Opposite.op ⦋0⦌) (ULift.up (nerveVertex n)))) := by
  let F := sigmaPresheafVertexFunctor v
  obtain ⟨c, hc, ⟨e⟩⟩ := presheafBarObject_realization F
  have hLc := mapJoinCocone_isColimit_of_adjunction_of_quasicategoryShape
    (sigmaReflectorAdjunction β hβ) c hc
  obtain ⟨ε, hε⟩ := sigmaReflector_exists_counit β hβ
  have := sigmaReflector_counit_isIso β hβ ε hε
  let eε : FunctorIso (sigmaPresheafInfinityInclusion C ≫ L) (𝟙 _) := asIso ε
  have hv : functorVertex F =
      (sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌) v :=
    sigmaPresheafVertexFunctor_vertex v
  let ev : VertexIso (mapJoinCocone L c).vertex v :=
    eqToIso (congrArg HomotopyCategory.mk (mapJoinCocone_vertex L c)) ≪≫
      VertexIso.map e L ≪≫
      eqToIso (congrArg HomotopyCategory.mk (congrArg (L.app (Opposite.op ⦋0⦌)) hv)) ≪≫
      eε.app v
  exact ⟨mapJoinCocone L c, hLc, ⟨ev⟩, fun n ↦ sigmaReflector_barDegree_isInd hC β hβ F n⟩

end SerrePositivity.InfinityCategories.F2.Presentable
