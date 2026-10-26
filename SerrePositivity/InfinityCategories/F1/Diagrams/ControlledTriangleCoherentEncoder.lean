module

public import SerrePositivity.InfinityCategories.F1.Diagrams.ControlledTriangleCoherentReconstruction
public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleFamilyHornPullback

/-!
概要：標準全対角を持つ普遍再構成族を、元の全ホーン a の実 fiber へ登録する。
方針：二短辺の厳密回収から全ホーンを回収し、同じ全族を curry する。
規約：実 encode : L ⟶ T を構成する。単射性・厳密切断はこの葉に含めない。
使われ方：採用済み正規化の全対角式を、元の固定ホーン空間へ供給する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (X Y Z : KanObject.{u}) (K : SSet.{u + 1})
  (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
  (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))
  (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ SpaceInfinity.{u})
  (hf : (horn₂₁.ι₀₁ ▷ K) ≫ a =
    (Δ[1] ◁ f) ≫ intervalMappingUncurry (coherentHomIntervalComparison X Y))
  (hg : (horn₂₁.ι₁₂ ▷ K) ≫ a =
    (Δ[1] ◁ g) ≫ intervalMappingUncurry (coherentHomIntervalComparison Y Z))

include hf hg in
lemma controlledTriangleCoherentFamily_horn :
    let L := controlledTriangleLongHomSpace X Z K (controlledTriangleCompositeFamily X Y Z K f g)
    ((horn 2 (1 : Fin 3)).ι ▷ (K ⊗ L)) ≫ controlledTriangleCoherentFamily X Y Z K f g =
      ((Λ[2, 1] : SSet.{u + 1}) ◁ fst K L) ≫ a := by
  dsimp only
  apply triangleFamily_horn_pullback (f ≫ coherentHomIntervalComparison X Y)
    (g ≫ coherentHomIntervalComparison Y Z) _ a
  · exact (controlledTriangleCoherentFamily_first X Y Z K f g).trans
      (congrArg intervalMappingUncurry (Category.assoc _ f (coherentHomIntervalComparison X Y)))
  · exact (controlledTriangleCoherentFamily_last X Y Z K f g).trans
      (congrArg intervalMappingUncurry (Category.assoc _ g (coherentHomIntervalComparison Y Z)))
  · exact hf.trans (intervalMappingUncurry_precomp f (coherentHomIntervalComparison X Y)).symm
  · exact hg.trans (intervalMappingUncurry_precomp g (coherentHomIntervalComparison Y Z)).symm

/-- 元の全族の fiber 登録前の curry。 -/
def controlledTriangleCoherentEncoderRaw :
    controlledTriangleLongHomSpace X Z K (controlledTriangleCompositeFamily X Y Z K f g) ⟶
      (ihom ((Δ[2] : SSet.{u + 1}) ⊗ K)).obj SpaceInfinity.{u} :=
  curry ((α_ (Δ[2] : SSet.{u + 1}) K _).hom ≫ controlledTriangleCoherentFamily X Y Z K f g)

include hf hg in
lemma controlledTriangleCoherentEncoderRaw_horn :
    controlledTriangleCoherentEncoderRaw X Y Z K f g ≫
      (pre ((horn 2 (1 : Fin 3)).ι ▷ K)).app SpaceInfinity.{u} =
        SSet.const (functorVertex a) := by
  exact triangleFamily_curry_horn (controlledTriangleCoherentFamily X Y Z K f g) a
    (controlledTriangleCoherentFamily_horn X Y Z K f g a hf hg)

/-- 同じ標準全対角を持つ実 L → T。単射性と厳密切断は別途。 -/
def controlledTriangleCoherentEncoder :
    controlledTriangleLongHomSpace X Z K (controlledTriangleCompositeFamily X Y Z K f g) ⟶
      controlledTriangleFamilySpace K a :=
  vertexFiberLift _ (functorVertex a) (controlledTriangleCoherentEncoderRaw X Y Z K f g)
    (controlledTriangleCoherentEncoderRaw_horn X Y Z K f g a hf hg)

lemma controlledTriangleCoherentEncoder_ι :
    controlledTriangleCoherentEncoder X Y Z K f g a hf hg ≫
      vertexFiberι ((pre ((horn 2 (1 : Fin 3)).ι ▷ K)).app SpaceInfinity.{u}) (functorVertex a) =
        controlledTriangleCoherentEncoderRaw X Y Z K f g :=
  vertexFiberLift_ι _ _ _ _

end SerrePositivity.InfinityCategories
