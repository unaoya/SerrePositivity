module
public import SerrePositivity.KST.SConstruction.NecklacePreferredForm
public import SerrePositivity.KST.SConstruction.NecklaceVertices
public import SerrePositivity.KST.SConstruction.NecklaceWedgePushout

/-! # preferred bead wedge と元の実単体集合の比較
概要：全 necklace の bead 分解を実単体集合へ移し、元の両端を保つ。
方針：形の等号を移送し、各連結の実押し出しを標準単体へ移す。
規約：点と bead は元の標準単体。使われ方：cubical rigidification の全添字の正当化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.NecklaceShape
open CategoryTheory Limits Simplicial SSet

/-- 同じ形の元の実単体集合の、全単体を保つ移送同型。 -/
def carrierCongr {T U : NecklaceShape} (h : T = U) : T.carrier.{u} ≅ U.carrier.{u} :=
  eqToIso (congrArg (carrier.{u}) h)

/-- 形の移送同型は元の始零単体を厳密に回収する。 -/
lemma carrierCongr_first {T U : NecklaceShape} (h : T = U) :
    (carrierCongr.{u} h).hom.app _ T.firstVertex = U.firstVertex := by
  cases h
  rfl

/-- 形の移送同型は元の終零単体を厳密に回収する。 -/
lemma carrierCongr_last {T U : NecklaceShape} (h : T = U) :
    (carrierCongr.{u} h).hom.app _ T.lastVertex = U.lastVertex := by
  cases h
  rfl

/-- 元の全 necklace の実単体集合と、選んだ preferred bead wedge との同型。 -/
def preferredCarrierIso (T : NecklaceShape) : T.carrier.{u} ≅ (ofBeads T.beads).carrier.{u} :=
  carrierCongr T.ofBeads_beads.symm

/-- preferred form への同型は元の始頂点を保つ。 -/
lemma preferredCarrierIso_first (T : NecklaceShape) :
    T.preferredCarrierIso.{u}.hom.app _ T.firstVertex = (ofBeads T.beads).firstVertex :=
  carrierCongr_first _

/-- preferred form への同型は元の終頂点を保つ。 -/
lemma preferredCarrierIso_last (T : NecklaceShape) :
    T.preferredCarrierIso.{u}.hom.app _ T.lastVertex = (ofBeads T.beads).lastVertex :=
  carrierCongr_last _

/-- 一つの bead の標準単体同型は、元の部分複体の包含そのもの。 -/
lemma singleSimplexIso_hom_eq_inclusion (n : ℕ) :
    (singleSimplexIso.{u} n).hom = (single n).inclusion := rfl

/-- 各 bead の連結は、元の標準零単体と標準 n 単体を使う実押し出し。 -/
theorem singleWedgeStandard_isPushout (n : ℕ) (U : NecklaceShape) :
    IsPushout
      ((singleSimplexIso.{u} 0).inv ≫ (single n).pointMap (single n).last ≫
        (singleSimplexIso n).hom)
      ((singleSimplexIso 0).inv ≫ U.pointMap U.first)
      ((singleSimplexIso n).inv ≫ (single n).wedgeInl U)
      ((single n).wedgeInr U) := by
  apply ((single n).wedge_isPushout.{u} U).of_iso (singleSimplexIso 0)
    (singleSimplexIso n) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- preferred form の各非空段は、元の標準 bead を終始点で貼る実押し出し。 -/
theorem ofBeads_cons_isPushout (n : ℕ) (ns : List ℕ) :
    IsPushout
      ((singleSimplexIso.{u} 0).inv ≫ (single n).pointMap (single n).last ≫
        (singleSimplexIso n).hom)
      ((singleSimplexIso 0).inv ≫ (ofBeads ns).pointMap (ofBeads ns).first)
      ((singleSimplexIso n).inv ≫ (single n).wedgeInl (ofBeads ns))
      ((single n).wedgeInr (ofBeads ns)) :=
  singleWedgeStandard_isPushout n (ofBeads ns)

end SerrePositivity.KST.SConstruction.NecklaceShape
