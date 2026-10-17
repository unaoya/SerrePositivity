module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionTriangles
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionRepresentable
public import SerrePositivity.DifferentialGraded.Perfect.UniversalProperty
public import SerrePositivity.DifferentialGraded.Perfect.CompactConverse

/-! # graph導来延長のperfect・compact対象の保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)
local instance : (dgDerivedExtension A D E F).CommShift ℤ := dgDerivedExtensionCommShift A D E F
local instance : (dgDerivedExtension A D E F).IsTriangulated :=
  dgDerivedExtensionIsTriangulated A D E F

lemma dgDerivedExtension_perfect {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    modulePerfect A E ((dgDerivedExtension A D E F).obj X) := by
  let P := (modulePerfect A E).inverseImage (dgDerivedExtension A D E F)
  have : P.IsTriangulated := by dsimp [P]; infer_instance
  have : P.IsClosedUnderIsomorphisms := by dsimp [P]; infer_instance
  have : P.IsStableUnderRetracts :=
    ⟨fun r hY => (modulePerfect A E).prop_of_retract (r.map (dgDerivedExtension A D E F)) hY⟩
  apply ((modulePerfect_le_iff_generators A D P).2 ?_) X hX
  intro d
  exact (modulePerfect A E).prop_of_iso (dgDerivedExtensionRepresentableIso A D E F d).symm
    (modulePerfectOver_representable A E (F.obj d) (Set.mem_univ _))

/-- U13dのcompact⇒perfectを再利用する。追加のcompact生成入力は要らない。 -/
lemma dgDerivedExtension_compact {X : DerivedModuleCategory A D} (hX : moduleCompact A D X) :
    moduleCompact A E ((dgDerivedExtension A D E F).obj X) :=
  modulePerfect_compact A E (dgDerivedExtension_perfect A D E F (moduleCompact_perfect A D hX))

end SerrePositivity.DifferentialGraded
