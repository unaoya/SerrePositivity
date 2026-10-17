module
public import SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceTriangles

/-! # U16b：擬同値の実際の延長・制限を主Perfへ制限する

U13のPerfの最小性と既存の代表加群計算を使う。導来同値本体は変更しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)
local instance moritaPerfectQuasiEquivalenceLocal1 :
    (dgDerivedRestriction A D E F).CommShift ℤ := dgDerivedRestrictionCommShift A D E F
local instance moritaPerfectQuasiEquivalenceLocal2 :
    (dgDerivedRestriction A D E F).IsTriangulated :=
  dgDerivedRestrictionIsTriangulated A D E F

lemma quasiEquivalenceRestriction_perfect (hF : QuasiEquivalence F)
    {X : DerivedModuleCategory A E} (hX : modulePerfect A E X) :
    modulePerfect A D ((dgDerivedRestriction A D E F).obj X) := by
  let P := (modulePerfect A D).inverseImage (dgDerivedRestriction A D E F)
  have : P.IsTriangulated := by dsimp [P]; infer_instance
  have : P.IsClosedUnderIsomorphisms := by dsimp [P]; infer_instance
  have : P.IsStableUnderRetracts :=
    ⟨fun r hY => (modulePerfect A D).prop_of_retract (r.map (dgDerivedRestriction A D E F)) hY⟩
  apply ((modulePerfect_le_iff_generators A E P).2 ?_) X hX
  intro e
  obtain ⟨d, ⟨ed⟩⟩ := dgDerivedExtension_representable_essImage A D E F hF.2 e
  exact (modulePerfect A D).prop_of_iso
    ((dgFunctorDerivedEquivalence A D E F hF).unitIso.app _ ≪≫
      (dgDerivedRestriction A D E F).mapIso ed)
    (modulePerfectOver_representable A D d (Set.mem_univ _))

lemma quasiEquivalenceExtension_perfect_iff (hF : QuasiEquivalence F)
    (X : DerivedModuleCategory A D) :
    modulePerfect A E ((dgDerivedExtension A D E F).obj X) ↔ modulePerfect A D X := by
  constructor
  · intro h
    exact (modulePerfect A D).prop_of_iso
      ((dgFunctorDerivedEquivalence A D E F hF).unitIso.app X).symm
      (quasiEquivalenceRestriction_perfect A D E F hF h)
  · exact dgDerivedExtension_perfect A D E F

lemma quasiEquivalenceRestriction_perfect_iff (hF : QuasiEquivalence F)
    (X : DerivedModuleCategory A E) :
    modulePerfect A D ((dgDerivedRestriction A D E F).obj X) ↔ modulePerfect A E X := by
  constructor
  · intro h
    exact (modulePerfect A E).prop_of_iso
      ((dgFunctorDerivedEquivalence A D E F hF).counitIso.app X)
      (dgDerivedExtension_perfect A D E F h)
  · exact quasiEquivalenceRestriction_perfect A D E F hF

/-- 任意dg関手の既存延長の、実際の主Perfへの制限。 -/
def quasiEquivalencePerfectExtension : PerfectModuleCategory A D ⥤ PerfectModuleCategory A E :=
  (modulePerfect A E).lift (perfectModuleInclusion A D Set.univ ⋙ dgDerivedExtension A D E F)
    (fun X => dgDerivedExtension_perfect A D E F X.property)

def quasiEquivalencePerfectRestriction (hF : QuasiEquivalence F) :
    PerfectModuleCategory A E ⥤ PerfectModuleCategory A D :=
  (modulePerfect A D).lift (perfectModuleInclusion A E Set.univ ⋙ dgDerivedRestriction A D E F)
    (fun X => quasiEquivalenceRestriction_perfect A D E F hF X.property)

def quasiEquivalencePerfectExtensionInclusionIso :
    quasiEquivalencePerfectExtension A D E F ⋙ perfectModuleInclusion A E Set.univ ≅
      perfectModuleInclusion A D Set.univ ⋙ dgDerivedExtension A D E F := Iso.refl _

def quasiEquivalencePerfectRestrictionInclusionIso (hF : QuasiEquivalence F) :
    quasiEquivalencePerfectRestriction A D E F hF ⋙ perfectModuleInclusion A D Set.univ ≅
      perfectModuleInclusion A E Set.univ ⋙ dgDerivedRestriction A D E F := Iso.refl _

/-- 順逆とも元の実際の関手の制限。単位・余単位も元の導来同値の成分を保つ。 -/
def quasiEquivalencePerfectEquivalence (hF : QuasiEquivalence F) :
    PerfectModuleCategory A D ≌ PerfectModuleCategory A E where
  functor := quasiEquivalencePerfectExtension A D E F
  inverse := quasiEquivalencePerfectRestriction A D E F hF
  unitIso := NatIso.ofComponents
    (fun X => (modulePerfect A D).isoMk
      ((dgFunctorDerivedEquivalence A D E F hF).unitIso.app X.obj))
    (by intro X Y f; apply (modulePerfect A D).hom_ext
        exact (dgFunctorDerivedEquivalence A D E F hF).unitIso.hom.naturality f.hom)
  counitIso := NatIso.ofComponents
    (fun X => (modulePerfect A E).isoMk
      ((dgFunctorDerivedEquivalence A D E F hF).counitIso.app X.obj))
    (by intro X Y f; apply (modulePerfect A E).hom_ext
        exact (dgFunctorDerivedEquivalence A D E F hF).counitIso.hom.naturality f.hom)
  functor_unitIso_comp X := by
    apply (modulePerfect A E).hom_ext
    exact (dgFunctorDerivedEquivalence A D E F hF).functor_unitIso_comp X.obj

lemma quasiEquivalencePerfectUnit_inclusion (hF : QuasiEquivalence F)
    (X : PerfectModuleCategory A D) :
    (perfectModuleInclusion A D Set.univ).map
        ((quasiEquivalencePerfectEquivalence A D E F hF).unitIso.hom.app X) =
      (dgDerivedExtensionUnit A D E F).app X.obj := rfl

lemma quasiEquivalencePerfectCounit_inclusion (hF : QuasiEquivalence F)
    (X : PerfectModuleCategory A E) :
    (perfectModuleInclusion A E Set.univ).map
        ((quasiEquivalencePerfectEquivalence A D E F hF).counitIso.hom.app X) =
      (dgDerivedExtensionCounit A D E F).app X.obj := rfl

end SerrePositivity.DifferentialGraded
