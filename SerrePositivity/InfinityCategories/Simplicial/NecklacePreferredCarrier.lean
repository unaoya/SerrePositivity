module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Simplicial.NecklacePreferredForm
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceVertices
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceWedgePushout

/-! # preferred bead wedge と元の実単体集合の比較
概要：全 necklace の bead 分解を実単体集合へ移し、元の両端を保つ。
方針：形の等号を移送し、各連結の実押し出しを標準単体へ移す。
規約：点と bead は元の標準単体。使われ方：cubical rigidification の全添字の正当化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.NecklaceShape
end SerrePositivity.KST.SConstruction.NecklaceShape
namespace SerrePositivity.InfinityCategories.Simplicial.NecklaceShape
open _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape
open CategoryTheory Limits _root_.Simplicial SSet

/-- 同じ形の元の実単体集合の、全単体を保つ移送同型。 -/
def carrierCongr {T U : _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape} (h : T = U) : T.carrier.{u} ≅ U.carrier.{u} :=
  eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.carrier.{u}) h)

/-- 形の移送同型は元の始零単体を厳密に回収する。 -/
lemma carrierCongr_first {T U : _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape} (h : T = U) :
    (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.carrierCongr.{u} h).hom.app _ T.firstVertex = U.firstVertex := by
  cases h
  rfl

/-- 形の移送同型は元の終零単体を厳密に回収する。 -/
lemma carrierCongr_last {T U : _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape} (h : T = U) :
    (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.carrierCongr.{u} h).hom.app _ T.lastVertex = U.lastVertex := by
  cases h
  rfl

/-- 元の全 necklace の実単体集合と、選んだ preferred bead wedge との同型。 -/
def preferredCarrierIso (T : _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape) : T.carrier.{u} ≅ (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.ofBeads T.beads).carrier.{u} :=
  _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.carrierCongr T.ofBeads_beads.symm

/-- preferred form への同型は元の始頂点を保つ。 -/
lemma preferredCarrierIso_first (T : _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape) :
    T.preferredCarrierIso.{u}.hom.app _ T.firstVertex = (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.ofBeads T.beads).firstVertex :=
  _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.carrierCongr_first _

/-- preferred form への同型は元の終頂点を保つ。 -/
lemma preferredCarrierIso_last (T : _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape) :
    T.preferredCarrierIso.{u}.hom.app _ T.lastVertex = (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.ofBeads T.beads).lastVertex :=
  _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.carrierCongr_last _

/-- 一つの bead の標準単体同型は、元の部分複体の包含そのもの。 -/
lemma singleSimplexIso_hom_eq_inclusion (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.singleSimplexIso.{u} n).hom = (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.single n).inclusion := rfl

/-- 各 bead の連結は、元の標準零単体と標準 n 単体を使う実押し出し。 -/
theorem singleWedgeStandard_isPushout (n : ℕ) (U : _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape) :
    IsPushout
      ((_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.singleSimplexIso.{u} 0).inv ≫ (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.single n).pointMap (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.single n).last ≫
        (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.singleSimplexIso n).hom)
      ((_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.singleSimplexIso 0).inv ≫ U.pointMap U.first)
      ((_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.singleSimplexIso n).inv ≫ (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.single n).wedgeInl U)
      ((_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.single n).wedgeInr U) := by
  apply ((_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.single n).wedge_isPushout.{u} U).of_iso (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.singleSimplexIso 0)
    (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.singleSimplexIso n) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- preferred form の各非空段は、元の標準 bead を終始点で貼る実押し出し。 -/
theorem ofBeads_cons_isPushout (n : ℕ) (ns : List ℕ) :
    IsPushout
      ((_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.singleSimplexIso.{u} 0).inv ≫ (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.single n).pointMap (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.single n).last ≫
        (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.singleSimplexIso n).hom)
      ((_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.singleSimplexIso 0).inv ≫ (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.ofBeads ns).pointMap (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.ofBeads ns).first)
      ((_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.singleSimplexIso n).inv ≫ (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.single n).wedgeInl (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.ofBeads ns))
      ((_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.single n).wedgeInr (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.ofBeads ns)) :=
  _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.singleWedgeStandard_isPushout n (_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.ofBeads ns)

end SerrePositivity.InfinityCategories.Simplicial.NecklaceShape

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.carrierCongr (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.carrierCongr := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.carrierCongr

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.carrierCongr_first := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.carrierCongr_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.carrierCongr_last := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.carrierCongr_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.ofBeads_cons_isPushout := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.ofBeads_cons_isPushout

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.preferredCarrierIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.preferredCarrierIso := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.preferredCarrierIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.preferredCarrierIso_first := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.preferredCarrierIso_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.preferredCarrierIso_last := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.preferredCarrierIso_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.singleSimplexIso_hom_eq_inclusion := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.singleSimplexIso_hom_eq_inclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.singleWedgeStandard_isPushout := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.singleWedgeStandard_isPushout

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.NecklaceShape.preferredCarrierIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.preferredCarrierIso._proof_1
