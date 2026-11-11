module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledTriangleCoherentEncoderNative
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledTriangleFamilyComparison

/-!
概要：採用済みの可逆切断比較を持つ制御二胞体族を、全パラメーターで供給する。
方針：実 coherent encoder と native Hom 読出しを、二つの可縮 Kan fiber の全族比較で結ぶ。
規約：切断は encode≫longHom から恒等への FunctorIso。native Hom・短辺・正規化全対角は
従来の厳密な回収式のまま保持し、同じ固定ホーン内の VertexIso と固定三面比較も供給する。
使われ方：Ind-S (9) のユーザー採用仕様、K-B の共有対角の貼り合わせ。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 全族の可逆切断比較を持つ、採用済みの制御二胞体供給要求。 -/
def ControlledTriangleNormalizedFamilyRequest : Prop :=
  ∀ (X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (K : SSet.{u + 1})
    (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
    (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))
    (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}),
    (horn₂₁.ι₀₁ ▷ K) ≫ a = (Δ[1] ◁ f) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y) →
    (horn₂₁.ι₁₂ ▷ K) ≫ a = (Δ[1] ◁ g) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison Y Z) →
  let P := SimplicialThickening.Path
    (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)
  let p : P :=
    { I := Set.univ
      left := Set.mem_univ _
      right := Set.mem_univ _
      left_le := fun k _ => Fin.zero_le k.down
      le_right := fun k _ => Fin.le_last k.down }
  let Pu := (SSet.uliftFunctor.{u + 1, u}).obj (nerve P)
  let H := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z)
  let c := lift f g ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, u + 1}
    (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (eComp SSet.{u} X Y Z)
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((ihom K).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (X := Pu) (Y := H) (ULift.up (ComposableArrows.mk₀ p))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c)
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre ((horn 2 (1 : Fin 3)).ι ▷ K)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  ∃ (encode : L ⟶ T) (longHom : T ⟶ L),
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (encode ≫ longHom) (𝟙 L)) ∧
    (∀ (t : T _⦋0⦌) (k : K _⦋0⦌),
      let Lt := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K ((ihom Pu).obj H)).symm
        ((longHom.app (Opposite.op ⦋0⦌) t).val)
      let Tt := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[2] ⊗ K) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm t.val
      let s := SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[2] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm
        ((curry Tt).app (Opposite.op ⦋0⦌) k))
      HEq (Lt.app (Opposite.op ⦋0⦌) k)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
          (s.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))) ∧
    (∀ t : T _⦋0⦌,
      let direct : P :=
        { I := {ULift.up 0, ULift.up 2}
          left := by simp
          right := by simp
          left_le := fun k _ => Fin.zero_le k.down
          le_right := fun k _ => Fin.le_last k.down }
      let Lt := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K ((ihom Pu).obj H)).symm
        ((longHom.app (Opposite.op ⦋0⦌) t).val)
      let nt := encode.app (Opposite.op ⦋0⦌) (longHom.app (Opposite.op ⦋0⦌) t)
      let Tt := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (Δ[2] ⊗ K) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).symm nt.val
      (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ Tt =
        (Δ[1] ◁ (Lt ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
          (X := Pu) (Y := H) (ULift.up (ComposableArrows.mk₀ direct)))) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Z)) ∧
    (∀ t : T _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso t
      (encode.app (Opposite.op ⦋0⦌) (longHom.app (Opposite.op ⦋0⦌) t)))) ∧
    (∀ b : (Λ[3, 2] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u},
      let E := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre ((horn 3 (2 : Fin 4)).ι ▷ K)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b)
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E ∧ ∀ old controlled : E _⦋0⦌,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso old controlled))

/-- 全パラメーターでの実供給。比較の向きは encode≫longHom から恒等。 -/
theorem controlledTriangleNormalizedFamilySupply : ControlledTriangleNormalizedFamilyRequest.{u} := by
  intro X Y Z K f g a hf hg
  dsimp only
  obtain ⟨r, hr⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleReadoutMap_exists X Y Z K f g a hf hg
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder X Y Z K f g a hf hg
  refine ⟨e, r, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilyMaps_readEncodeIso X Z K
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g) a e r⟩, ?_, ?_, ?_, ?_⟩
  · intro t k
    erw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.curry_app_vertex, show (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[2] _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilyValue t) k)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilyValue t) k from
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply _]
    exact hr t k
  · intro t
    have hd : (
        { I := {ULift.up 0, ULift.up 2}
          left := by simp
          right := by simp
          left_le := fun k _ => Fin.zero_le k.down
          le_right := fun k _ => Fin.le_last k.down } : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleDirectPath := by
      apply SimplicialThickening.Path.ext
      ext ⟨j⟩
      simp [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleDirectPath, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathFromInterval]
    rw [hd]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentNormalization_diagonal X Y Z K f g a hf hg r t
  · intro t
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentNormalization_vertexIso X Y Z K f g a hf hg r t
  · intro b
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronFamilyExtensionSpace_compare K b

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
