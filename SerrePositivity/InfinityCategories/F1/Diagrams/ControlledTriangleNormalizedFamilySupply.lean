module

public import SerrePositivity.InfinityCategories.F1.Diagrams.ControlledTriangleCoherentEncoderNative
public import SerrePositivity.InfinityCategories.F1.Diagrams.ControlledTriangleFamilyComparison

/-!
概要：採用済みの可逆切断比較を持つ制御二胞体族を、全パラメーターで供給する。
方針：実 coherent encoder と native Hom 読出しを、二つの可縮 Kan fiber の全族比較で結ぶ。
規約：切断は encode≫longHom から恒等への FunctorIso。native Hom・短辺・正規化全対角は
従来の厳密な回収式のまま保持し、同じ固定ホーン内の VertexIso と固定三面比較も供給する。
使われ方：Ind-S (9) のユーザー採用仕様、K-B の共有対角の貼り合わせ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 全族の可逆切断比較を持つ、採用済みの制御二胞体供給要求。 -/
def ControlledTriangleNormalizedFamilyRequest : Prop :=
  ∀ (X Y Z : KanObject.{u}) (K : SSet.{u + 1})
    (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
    (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))
    (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u}),
    (horn₂₁.ι₀₁ ▷ K) ≫ a = (Δ[1] ◁ f) ≫
      intervalMappingUncurry (coherentHomIntervalComparison X Y) →
    (horn₂₁.ι₁₂ ▷ K) ≫ a = (Δ[1] ◁ g) ≫
      intervalMappingUncurry (coherentHomIntervalComparison Y Z) →
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
  let c := lift f g ≫ (HomotopyLimits.uliftTensorIso.{u, u + 1}
    (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (eComp SSet.{u} X Y Z)
  let L := vertexFiber ((ihom K).map
    (evaluateFunctorAt (X := Pu) (Y := H) (ULift.up (ComposableArrows.mk₀ p))))
    (functorVertex c)
  let T := vertexFiber ((pre ((horn 2 (1 : Fin 3)).ι ▷ K)).app SpaceInfinity.{u})
    (functorVertex a)
  ∃ (encode : L ⟶ T) (longHom : T ⟶ L),
    Nonempty (FunctorIso (encode ≫ longHom) (𝟙 L)) ∧
    (∀ (t : T _⦋0⦌) (k : K _⦋0⦌),
      let Lt := (functorVertexEquiv K ((ihom Pu).obj H)).symm
        ((longHom.app (Opposite.op ⦋0⦌) t).val)
      let Tt := (functorVertexEquiv (Δ[2] ⊗ K) SpaceInfinity.{u}).symm t.val
      let s := SSet.yonedaEquiv ((functorVertexEquiv Δ[2] SpaceInfinity.{u}).symm
        ((curry Tt).app (Opposite.op ⦋0⦌) k))
      HEq (Lt.app (Opposite.op ⦋0⦌) k)
        (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
          (s.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))) ∧
    (∀ t : T _⦋0⦌,
      let direct : P :=
        { I := {ULift.up 0, ULift.up 2}
          left := by simp
          right := by simp
          left_le := fun k _ => Fin.zero_le k.down
          le_right := fun k _ => Fin.le_last k.down }
      let Lt := (functorVertexEquiv K ((ihom Pu).obj H)).symm
        ((longHom.app (Opposite.op ⦋0⦌) t).val)
      let nt := encode.app (Opposite.op ⦋0⦌) (longHom.app (Opposite.op ⦋0⦌) t)
      let Tt := (functorVertexEquiv (Δ[2] ⊗ K) SpaceInfinity.{u}).symm nt.val
      (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ Tt =
        (Δ[1] ◁ (Lt ≫ evaluateFunctorAt
          (X := Pu) (Y := H) (ULift.up (ComposableArrows.mk₀ direct)))) ≫
            intervalMappingUncurry (coherentHomIntervalComparison X Z)) ∧
    (∀ t : T _⦋0⦌, Nonempty (VertexIso t
      (encode.app (Opposite.op ⦋0⦌) (longHom.app (Opposite.op ⦋0⦌) t)))) ∧
    (∀ b : (Λ[3, 2] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u},
      let E := vertexFiber ((pre ((horn 3 (2 : Fin 4)).ι ▷ K)).app SpaceInfinity.{u})
        (functorVertex b)
      IsContractibleKan E ∧ ∀ old controlled : E _⦋0⦌,
        Nonempty (VertexIso old controlled))

/-- 全パラメーターでの実供給。比較の向きは encode≫longHom から恒等。 -/
theorem controlledTriangleNormalizedFamilySupply : ControlledTriangleNormalizedFamilyRequest.{u} := by
  intro X Y Z K f g a hf hg
  dsimp only
  obtain ⟨r, hr⟩ := controlledTriangleReadoutMap_exists X Y Z K f g a hf hg
  let e := controlledTriangleCoherentEncoder X Y Z K f g a hf hg
  refine ⟨e, r, ⟨controlledTriangleFamilyMaps_readEncodeIso X Z K
    (controlledTriangleCompositeFamily X Y Z K f g) a e r⟩, ?_, ?_, ?_, ?_⟩
  · intro t k
    erw [curry_app_vertex, show (functorVertexEquiv Δ[2] SpaceInfinity).symm
      (functorVertex (familyAtVertex (controlledTriangleFamilyValue t) k)) =
        familyAtVertex (controlledTriangleFamilyValue t) k from
          (functorVertexEquiv _ _).symm_apply_apply _]
    exact hr t k
  · intro t
    have hd : (
        { I := {ULift.up 0, ULift.up 2}
          left := by simp
          right := by simp
          left_le := fun k _ => Fin.zero_le k.down
          le_right := fun k _ => Fin.le_last k.down } : TriangleNativePath.{u}) =
        triangleDirectPath := by
      apply SimplicialThickening.Path.ext
      ext ⟨j⟩
      simp [triangleDirectPath, trianglePathFromInterval]
    rw [hd]
    exact controlledTriangleCoherentNormalization_diagonal X Y Z K f g a hf hg r t
  · intro t
    exact controlledTriangleCoherentNormalization_vertexIso X Y Z K f g a hf hg r t
  · intro b
    exact tetrahedronFamilyExtensionSpace_compare K b

end SerrePositivity.InfinityCategories
