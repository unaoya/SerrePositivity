module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledTriangleCoherentEncoderNative
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledTriangleSplitReduction

/-!
概要：採用済みの正規化要求を、構成済み coherent encoder の単射性へ還元する。
方針：単射 encoder への厳密左逆を頂点関係つきで選び、全対角と同じ固定ホーン内の
可逆比較を接続する。
規約：単射性は明示的な未供給入力であり、この葉は (9) の無条件の完了を主張しない。
使われ方：K-B の採用済み要求型との最終的な型照合。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 採用済みの要求全体。厳密切断の条項も保持する。 -/
def ControlledTriangleNormalizedRequest : Prop :=
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
    encode ≫ longHom = 𝟙 L ∧
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

/-- 実 coherent encoder の単射性が供給されれば、全要求を同じ二写像で満たす。 -/
lemma controlledTriangleNormalizedRequest_of_mono
    (hmono : ∀ (X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (K : SSet.{u + 1})
      (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
      (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))
      (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (hf : (horn₂₁.ι₀₁ ▷ K) ≫ a =
        (Δ[1] ◁ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y))
      (hg : (horn₂₁.ι₁₂ ▷ K) ≫ a =
        (Δ[1] ◁ g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison Y Z)),
      Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder X Y Z K f g a hf hg)) :
    ControlledTriangleNormalizedRequest.{u} := by
  intro X Y Z K f g a hf hg
  dsimp only
  letI := hmono X Y Z K f g a hf hg
  obtain ⟨r, hs, hr⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleSplit_of_mono_encoder X Y Z K f g a hf hg
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder X Y Z K f g a hf hg)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder_native X Y Z K f g a hf hg)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCoherentEncoder X Y Z K f g a hf hg
  refine ⟨e, r, hs, ?_, ?_, ?_, ?_⟩
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
