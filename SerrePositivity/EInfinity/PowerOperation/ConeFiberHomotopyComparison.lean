module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLanePointedConeFiber
public import SerrePositivity.EInfinity.PowerOperation.PointedHomotopyIso

/-!
# cone の指定 kernel 比較によるホモトピー写像の全単射性の移送

DAG XIII §2.2 の Ω 比較への前段。複体射の kernel を変えず、自然変換の指定射を移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits CochainComplex SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.DifferentialGraded
open SerrePositivity.KST.Spectra (pointedHomotopyMap pointedHomotopyMap_comp)
variable (A : Type u) [CommRing A]
variable (F G : Complex A ⥤ PointedSimplicialSet.{u})
  [PreservesFiniteLimits F] [F.PreservesZeroMorphisms]
  [PreservesFiniteLimits G] [G.PreservesZeroMorphisms]
  [∀ M, KanComplex (F.obj M).right] [∀ M, KanComplex (G.obj M).right]

/-- 自然変換の元の射の全単射性は、指定 cone fiber の射の全単射性と同値。 -/
lemma coneFiberHomotopyMap_bijective_iff (η : F ⟶ G) {M N : Complex A} (f : M ⟶ N)
    [Fibration (F.map (mappingCone.triangle f).mor₃).right]
    [Fibration (G.map (mappingCone.triangle f).mor₃).right] (n : ℕ) :
    Function.Bijective (pointedHomotopyMap n (η.app N)) ↔
      Function.Bijective (pointedHomotopyMap n
        (KST.Spectra.PointedFiberComparison.map (F.map (mappingCone.triangle f).mor₃)
          (G.map (mappingCone.triangle f).mor₃)
          (η.app (mappingCone f)) (η.app (M⟦(1 : ℤ)⟧))
          (η.naturality (mappingCone.triangle f).mor₃))) := by
  let eF := pointedConeFiberIso A F f
  let eG := pointedConeFiberIso A G f
  let φ := KST.Spectra.PointedFiberComparison.map (F.map (mappingCone.triangle f).mor₃)
    (G.map (mappingCone.triangle f).mor₃)
    (η.app (mappingCone f)) (η.app (M⟦(1 : ℤ)⟧))
    (η.naturality (mappingCone.triangle f).mor₃)
  have h : pointedHomotopyMap n φ ∘ pointedHomotopyMap n eF.hom =
      pointedHomotopyMap n eG.hom ∘ pointedHomotopyMap n (η.app N) := by
    funext a
    dsimp only [Function.comp_apply]
    rw [← pointedHomotopyMap_comp, ← pointedHomotopyMap_comp]
    exact congrArg (fun k => pointedHomotopyMap n k a)
      (pointedConeFiberIso_naturality A F G η f)
  have hF := (pointedIsoHomotopyEquiv eF n).bijective
  have hG := (pointedIsoHomotopyEquiv eG n).bijective
  change Function.Bijective (pointedHomotopyMap n (η.app N)) ↔
    Function.Bijective (pointedHomotopyMap n φ)
  exact (Function.Bijective.of_comp_iff' hG _).symm.trans
    ((Iff.of_eq (congrArg Function.Bijective h)).symm.trans
      (Function.Bijective.of_comp_iff _ hF))

end SerrePositivity.EInfinity.PowerOperation
