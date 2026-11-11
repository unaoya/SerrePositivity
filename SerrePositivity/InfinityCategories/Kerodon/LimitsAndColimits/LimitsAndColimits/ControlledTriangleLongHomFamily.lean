module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledTriangleFamilyVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.NativeLongHomFamilyVertices

/-!
概要：合成端を固定した全長 Hom 全族から、同じ短辺の実二胞体族を構成する。
方針：各入力点の小さい native Hom を読み、全ホーンを固定した零骨格指定延長を取る。
規約：全族空間間の単射 encode や厳密左逆はまだ主張しない。
使われ方：Ind-S (9) の L の各頂点から実制御二胞体族への構成。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 標的の厳密な移送と元の射の HEq は、宇宙を上げた全関手頂点の HEq を与える。 -/
lemma uliftHomFunctorVertex_heq {A H H' : SSet.{u}} (hH : H = H')
    (f : A ⟶ H) (g : A ⟶ H') (h : HEq f g) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{v, u}).map f))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{v, u}).map g)) := by
  subst H'
  obtain rfl := eq_of_heq h
  rfl

/-- 合成端を全入力で固定した長い Hom 全族の各入力を厳密回収する実二胞体族。 -/
lemma controlledTriangleFamily_exists_of_longHom
    (X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (K : SSet.{u + 1})
    (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
    (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))
    (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hf : (horn₂₁.ι₀₁ ▷ K) ≫ a =
      (Δ[1] ◁ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y))
    (hg : (horn₂₁.ι₁₂ ▷ K) ≫ a =
      (Δ[1] ◁ g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison Y Z))
    (q : K ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj
      ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z)))
    (hq : q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))
      (Y := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
      (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath)) =
        lift f g ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1}
          (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
          (SSet.uliftFunctor.{u + 1, u}).map (eComp SSet.{u} X Y Z)) :
    ∃ F : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u},
      ((horn 2 (1 : Fin 3)).ι ▷ K) ≫ F = a ∧
      ∀ k : K _⦋0⦌,
        HEq (q.app (Opposite.op ⦋0⦌) k)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
            ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex F k)).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) := by
  have hm (k : K _⦋0⦌) :
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nativeHomFamilyValue q k).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath) =
        SimplicialCategory.homEquiv' X Z
          (((SimplicialCategory.homEquiv' X Y).symm (f.app (Opposite.op ⦋0⦌) k).down) ≫
           ((SimplicialCategory.homEquiv' Y Z).symm (g.app (Opposite.op ⦋0⦌) k).down)) := by
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nativeHomFamilyValue_evaluate q
      (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath) _ hq k
    have hh := congrArg ULift.down he
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nativeHomFamilyValue q k).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath) =
        (eComp SSet X Y Z).app (Opposite.op ⦋0⦌)
          ((f.app (Opposite.op ⦋0⦌) k).down, (g.app (Opposite.op ⦋0⦌) k).down) at hh
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_vertex_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hh
  obtain ⟨F, hF, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamily_exists_with_native_vertices
    X Y Z K f g a hf hg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nativeHomFamilyValue q) hm
  refine ⟨F, hF, ?_⟩
  intro k
  obtain ⟨hX, hZ, hnative⟩ := hv k
  have he := uliftHomFunctorVertex_heq.{u, u + 1}
    (congrArg₂ SimplicialCategory.sHom hX hZ) _ _ hnative
  exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nativeHomFamilyValue_vertex q k).symm).trans he.symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
