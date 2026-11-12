module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGExactValues
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.ExactEnrichment

/-! # 全 native dg 入力族の完全関手空間への持ち上げ
概要：元の実 Perf 関手族の全単体を、完全関手の充満部分 ∞ 圏へ持ち上げる。
方針：各入力頂点から同じ厳密 dg 射を回収し、元の native 作用の完全性を使う。
規約：離散 Hom へ置換しない。使われ方：全高次入力を保つ厳密豊穣 Perf 関手。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

private lemma unitHomEquiv_comp {X Y : SSet.{w}} (f : 𝟙_ SSet.{w} ⟶ X) (g : X ⟶ Y) :
    SSet.unitHomEquiv Y (f ≫ g) = g.app (Opposite.op ⦋0⦌) (SSet.unitHomEquiv X f) := rfl

/-- 全 native 入力族の指定頂点は、同じ元の完全な dg Perf 射の関手頂点。 -/
lemma presentedPerfectDGNativeFamilyMap_vertex
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    (presentedPerfectDGNativeFamilyMap A C D).app (Opposite.op ⦋0⦌)
      (perfDGInputVertexEquiv A C D F) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction A C D F.down)) := by
  have h := congrArg (SSet.unitHomEquiv _)
    (presentedPerfectDGNativeFamilyMap_fixed A C D F.down)
  rw [unitHomEquiv_comp, ← perfDGInputUnitHomEquiv_point A C D F,
    perfDGInputUnitHomEquiv_vertex] at h
  exact h

/-- 元の全 native 関手族の全ての頂点は完全関手である。 -/
lemma presentedPerfectDGNativeFamilyMap_isExactVertex (C D : PerfDGInput.{u, v} A)
    (v : (presentedPerfectDGNativeParameter A C D) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsExactVertex
      (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D)
      ((presentedPerfectDGNativeFamilyMap A C D).app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨F, rfl⟩ := (perfDGInputVertexEquiv A C D).surjective v
  rw [presentedPerfectDGNativeFamilyMap_vertex]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _) (presentedPerfectDGExactMap A F).hom))
  rw [Equiv.symm_apply_apply]
  exact (presentedPerfectDGExactMap A F).isExact

/-- 元の全 native dg 入力族を、全自然変換を持つ完全関手空間へ持ち上げる。 -/
def presentedPerfectDGExactFamilyMap (C D : PerfDGInput.{u, v} A) :
    presentedPerfectDGNativeParameter A C D ⟶
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors
        (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D) :
          SSet.{max (u + 1) v}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsExactVertex
    (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D))
      (presentedPerfectDGNativeFamilyMap A C D)
      (presentedPerfectDGNativeFamilyMap_isExactVertex A C D)

/-- 完全関手空間の包含後には、元の関手族の全単体を回収する。 -/
lemma presentedPerfectDGExactFamilyMap_inclusion (C D : PerfDGInput.{u, v} A) :
    presentedPerfectDGExactFamilyMap A C D ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors
      (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D)).ι =
        presentedPerfectDGNativeFamilyMap A C D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 元の Kan 入力族の全単体を、完全関手空間の実 core へ持ち上げる。 -/
def presentedPerfectDGExactCoreFamilyMap (C D : PerfDGInput.{u, v} A) :
    presentedPerfectDGNativeParameter A C D ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors
        (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D) :
          SSet.{max (u + 1) v}) : SSet.{max (u + 1) v}) :=
  kanSourceCoreMap (presentedPerfectDGExactFamilyMap A C D)

/-- 二つの実包含の後で、元の native Perf 関手族を全単体で保持する。 -/
lemma presentedPerfectDGExactCoreFamilyMap_inclusion (C D : PerfDGInput.{u, v} A) :
    (presentedPerfectDGExactCoreFamilyMap A C D ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors
        (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D) :
          SSet.{max (u + 1) v})).ι) ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors
            (presentedPerfectDGStableCategory A C) (presentedPerfectDGStableCategory A D)).ι =
      presentedPerfectDGNativeFamilyMap A C D :=
  presentedPerfectDGExactFamilyMap_inclusion A C D

end SerrePositivity.KST.SConstruction
