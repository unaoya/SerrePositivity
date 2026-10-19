module
public import SerrePositivity.KST.SConstruction.FamilyChainPairing
public import SerrePositivity.KST.SConstruction.PointedFamilyConstantComposition

/-! # 二本の実補正列から作る合成族の実補正列
概要：置換射影を挟む二本の族の合成を、元の射の合成から実補正区間で結ぶ。
方針：前の補正列を元の後続射で写し、後ろの補正列を補正済みの前の族と組にして連結する。
規約：全区間の順序と全時刻を保持し、各段の成分だけで比較しない。
使われ方：K の BF 族の合成の raw 射影を元の合成射と照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.PointedMapping
open scoped Simplicial
local instance compositeCorrectionSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {U : SSet.{u}} {A B R C : PointedSimplicialSet.{u}}
  (p : B ⟶ R) (g : R ⟶ C) (f : A ⟶ R)
  (a : U ⟶ (PointedObject.basedHom A B).right)
  (b : U ⟶ (PointedObject.basedHom B C).right)
  (cf : FamilyHomotopyChain (SSet.const (familyVertex f))
    (a ≫ (PointedObject.basedHomMap A p).right))
  (cg : FamilyHomotopyChain (SSet.const (familyVertex (p ≫ g))) b)

/-- 二本の元の補正列から、合成の元の実補正列を順に構成する。 -/
def pointedCompositeCorrectionChain :
    FamilyHomotopyChain (SSet.const (familyVertex (f ≫ g))) (lift a b ≫ eComp SSet A B C) := by
  let c := familyHomotopyChainMap cf (PointedObject.basedHomMap A g).right
  let d := familyHomotopyChainMap (familyHomotopyChainPairLeft a cg) (eComp SSet A B C)
  have hs : SSet.const (X := U) (familyVertex (f ≫ g)) =
      SSet.const (familyVertex f) ≫ (PointedObject.basedHomMap A g).right := by
    rw [SSet.const_comp, familyVertex_post]
  have hm : (a ≫ (PointedObject.basedHomMap A p).right) ≫
      (PointedObject.basedHomMap A g).right =
        lift a (SSet.const (familyVertex (p ≫ g))) ≫ eComp SSet A B C := by
    rw [pointedFamilyComposition_const_right]
    simp only [← PointedEnrichment.whiskerLeft_eq, eHomWhiskerLeft_comp, Category.assoc]
  exact familyHomotopyChainSourceTransport
    (familyHomotopyChainAppend c (familyHomotopyChainSourceTransport d hm)) hs

/-- 合成補正の全 trace は、前後二本の元の全区間を順に合成したものである。 -/
lemma pointedCompositeCorrectionChain_trace :
    familyHomotopyChainTrace (pointedCompositeCorrectionChain p g f a b cf cg) =
      (familyHomotopyChainTrace cf).map (· ≫ (PointedObject.basedHomMap A g).right) ++
      (familyHomotopyChainTrace cg).map
        (fun h => (lift (fst U (Δ[1] : SSet.{u}) ≫ a) h ≫ eComp SSet A B C :
          U ⊗ (Δ[1] : SSet.{u}) ⟶ (PointedObject.basedHom A C).right)) := by
  simp only [pointedCompositeCorrectionChain, familyHomotopyChainSourceTransport_trace,
    familyHomotopyChainAppend_trace, familyHomotopyChainMap_trace,
    familyHomotopyChainPairLeft_trace, List.map_map, Function.comp_def]
  rfl

end SerrePositivity.KST.SConstruction
