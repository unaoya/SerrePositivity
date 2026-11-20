module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklacePreferredForm
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceVertices
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgePushout

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
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

open CategoryTheory Limits _root_.Simplicial SSet

/-- 同じ形の元の実単体集合の、全単体を保つ移送同型。 -/
def carrierCongr {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape} (h : T = U) : T.carrier.{u} ≅ U.carrier.{u} :=
  eqToIso (congrArg (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.carrier.{u}) h)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (carrierCongr)


/-- 形の移送同型は元の始零単体を厳密に回収する。 -/
lemma carrierCongr_first {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape} (h : T = U) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.carrierCongr.{u} h).hom.app _ T.firstVertex = U.firstVertex := by
  cases h
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (carrierCongr_first)


/-- 形の移送同型は元の終零単体を厳密に回収する。 -/
lemma carrierCongr_last {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape} (h : T = U) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.carrierCongr.{u} h).hom.app _ T.lastVertex = U.lastVertex := by
  cases h
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (carrierCongr_last)


/-- 元の全 necklace の実単体集合と、選んだ preferred bead wedge との同型。 -/
def preferredCarrierIso (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) : T.carrier.{u} ≅ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ofBeads T.beads).carrier.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.carrierCongr T.ofBeads_beads.symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (preferredCarrierIso)


/-- preferred form への同型は元の始頂点を保つ。 -/
lemma preferredCarrierIso_first (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) :
    T.preferredCarrierIso.{u}.hom.app _ T.firstVertex = (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ofBeads T.beads).firstVertex :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.carrierCongr_first _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (preferredCarrierIso_first)


/-- preferred form への同型は元の終頂点を保つ。 -/
lemma preferredCarrierIso_last (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) :
    T.preferredCarrierIso.{u}.hom.app _ T.lastVertex = (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ofBeads T.beads).lastVertex :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.carrierCongr_last _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (preferredCarrierIso_last)


/-- 一つの bead の標準単体同型は、元の部分複体の包含そのもの。 -/
lemma singleSimplexIso_hom_eq_inclusion (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso.{u} n).hom = (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n).inclusion := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (singleSimplexIso_hom_eq_inclusion)


/-- 各 bead の連結は、元の標準零単体と標準 n 単体を使う実押し出し。 -/
theorem singleWedgeStandard_isPushout (n : ℕ) (U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape) :
    IsPushout
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso.{u} 0).inv ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n).pointMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n).last ≫
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso n).hom)
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso 0).inv ≫ U.pointMap U.first)
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso n).inv ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n).wedgeInl U)
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n).wedgeInr U) := by
  apply ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n).wedge_isPushout.{u} U).of_iso (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso 0)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso n) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (singleWedgeStandard_isPushout)


/-- preferred form の各非空段は、元の標準 bead を終始点で貼る実押し出し。 -/
theorem ofBeads_cons_isPushout (n : ℕ) (ns : List ℕ) :
    IsPushout
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso.{u} 0).inv ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n).pointMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n).last ≫
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso n).hom)
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso 0).inv ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ofBeads ns).pointMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ofBeads ns).first)
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.singleSimplexIso n).inv ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n).wedgeInl (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ofBeads ns))
      ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single n).wedgeInr (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ofBeads ns)) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.singleWedgeStandard_isPushout n (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.ofBeads ns)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape export _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics (ofBeads_cons_isPushout)


end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
