module
public import SerrePositivity.KST.Fibration.ZeroFunctorLocus

/-! # 指定された零値完全関手族の全単体を保つ持ち上げと境界充填 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の完全関手の Kan Hom から、実関手・全自然変換の単体集合への包含。 -/
def stableHomAmbient (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (A ⟶[SSet.{u}] B) ⟶ (ihom A.obj).obj B.obj :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u})).ι ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B).ι

/-- Kan Hom の実頂点が、元の関手圏で零値関手を表すという条件。 -/
def StableHomZeroVertex (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) (v : (A ⟶[SSet.{u}] B) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((stableHomAmbient A B).app (Opposite.op ⦋0⦌) v)

/-- 元の零値部分複体からの Kan Hom の射は、全頂点で元の零値条件を保つ。 -/
theorem zeroFunctorLocusToStableHom_zero (A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u})
    (v : (zeroFunctorLocus A B) _⦋0⦌) :
    StableHomZeroVertex A B
      ((zeroFunctorLocusToStableHom A B).app (Opposite.op ⦋0⦌) v) := by
  have he := (Category.assoc (zeroFunctorLocusToStableHom A B)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u})).ι (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B).ι).symm.trans
      ((congrArg (fun f => f ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B).ι)
        (zeroFunctorLocusToStableHom_inclusion A B)).trans
          (zeroFunctorLocusToExact_inclusion A B))
  have hv := congrArg (fun f => f.app (Opposite.op ⦋0⦌) v) he
  change (stableHomAmbient A B).app (Opposite.op ⦋0⦌)
    ((zeroFunctorLocusToStableHom A B).app (Opposite.op ⦋0⦌) v) = v.val at hv
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((stableHomAmbient A B).app (Opposite.op ⦋0⦌)
    ((zeroFunctorLocusToStableHom A B).app (Opposite.op ⦋0⦌) v))
  exact hv.symm ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v

/-- 任意の実パラメータの零値完全関手族を、同じ零値部分複体へ持ち上げる。 -/
def zeroStableHomFamilyLift {T : SSet.{u}} {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    (H : T ⟶ (A ⟶[SSet.{u}] B))
    (hH : ∀ v, StableHomZeroVertex A B (H.app (Opposite.op ⦋0⦌) v)) :
    T ⟶ zeroFunctorLocus A B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (H ≫ stableHomAmbient A B) hH

/-- 元の Kan Hom へ戻すと、指定した全関手族そのものを厳密に回収する。 -/
theorem zeroStableHomFamilyLift_recovery {T : SSet.{u}} {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    (H : T ⟶ (A ⟶[SSet.{u}] B))
    (hH : ∀ v, StableHomZeroVertex A B (H.app (Opposite.op ⦋0⦌) v)) :
    zeroStableHomFamilyLift H hH ≫ zeroFunctorLocusToStableHom A B = H := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u})).ι).1
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B).ι).1
  have hi := congrArg (fun f => f ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B).ι)
    (zeroFunctorLocusToStableHom_inclusion A B)
  have he := hi.trans (zeroFunctorLocusToExact_inclusion A B)
  calc
    _ = zeroStableHomFamilyLift H hH ≫
        ((zeroFunctorLocusToStableHom A B ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B : SSet.{u})).ι) ≫
            (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A B).ι) := by simp only [Category.assoc]
    _ = zeroStableHomFamilyLift H hH ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom A.obj).obj B.obj) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex).ι :=
      congrArg (zeroStableHomFamilyLift H hH ≫ ·) he
    _ = H ≫ stableHomAmbient A B := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
    _ = _ := (Category.assoc _ _ _).symm

/-- 指定した零値完全関手の境界は、元の Kan Hom 内で零値条件を保って充填できる。 -/
theorem zeroStableHomBoundary_fill_zero {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (n : ℕ)
    (b : (boundary n : SSet.{u}) ⟶ (A ⟶[SSet.{u}] B))
    (hb : ∀ v, StableHomZeroVertex A B (b.app (Opposite.op ⦋0⦌) v)) :
    ∃ F : (Δ[n] : SSet.{u}) ⟶ (A ⟶[SSet.{u}] B), (boundary n).ι ≫ F = b ∧
      ∀ v, StableHomZeroVertex A B (F.app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨F, hF⟩ := zeroFunctorLocus_isContractibleKan A B n (zeroStableHomFamilyLift b hb)
  refine ⟨F ≫ zeroFunctorLocusToStableHom A B, ?_, ?_⟩
  · rw [← Category.assoc, hF]
    exact zeroStableHomFamilyLift_recovery b hb
  · intro v
    exact zeroFunctorLocusToStableHom_zero A B (F.app (Opposite.op ⦋0⦌) v)

/-- 指定した零値完全関手の境界は、元の Kan Hom 内で全次元にわたり充填できる。 -/
theorem zeroStableHomBoundary_fill {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (n : ℕ)
    (b : (boundary n : SSet.{u}) ⟶ (A ⟶[SSet.{u}] B))
    (hb : ∀ v, StableHomZeroVertex A B (b.app (Opposite.op ⦋0⦌) v)) :
    ∃ F : (Δ[n] : SSet.{u}) ⟶ (A ⟶[SSet.{u}] B), (boundary n).ι ≫ F = b := by
  obtain ⟨F, hF, _⟩ := zeroStableHomBoundary_fill_zero n b hb
  exact ⟨F, hF⟩

end SerrePositivity.KST.Fibration
