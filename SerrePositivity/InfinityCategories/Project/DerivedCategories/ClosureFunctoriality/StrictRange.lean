module
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Module.Disk
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
概要：閉包族の実 dg 同型による像を、加群演算に沿って閉じる。
方針：cone の射を両端同型で共役し、標準 cone 関手へ可換四角形を送る。
規約：同型は閉零射の逆を持ち、導来圏・ホモトピー圏の同型へ弱めない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (S : Set (ModuleCategory R D))

/-- 固定代表族を変えず、その実 dg 同型による飽和を性質として扱う。 -/
def dgModuleStrictRange (M : ModuleCategory R D) : Prop :=
  ∃ N, S N ∧ Nonempty (N ≅ M)

lemma dgModuleStrictRange_of_mem {M : ModuleCategory R D} (hM : S M) :
    dgModuleStrictRange R D S M := ⟨M, hM, ⟨Iso.refl _⟩⟩

lemma dgModuleStrictRange_of_iso {M N : ModuleCategory R D} (e : M ≅ N)
    (hM : dgModuleStrictRange R D S M) : dgModuleStrictRange R D S N := by
  obtain ⟨L, hL, ⟨h⟩⟩ := hM
  exact ⟨L, hL, ⟨h ≪≫ e⟩⟩

lemma dgModuleStrictRange_shift
    (hS : ∀ M, S M → ∀ s : ℤ, S (M⟦s⟧))
    {M : ModuleCategory R D} (hM : dgModuleStrictRange R D S M) (s : ℤ) :
    dgModuleStrictRange R D S (M⟦s⟧) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := hM
  exact ⟨N⟦s⟧, hS N hN s, ⟨(shiftFunctor (ModuleCategory R D) s).mapIso e⟩⟩

lemma dgModuleStrictRange_binary
    (hS : ∀ M N, S M → S N → S (M ⨿ N))
    {M N : ModuleCategory R D} (hM : dgModuleStrictRange R D S M)
    (hN : dgModuleStrictRange R D S N) : dgModuleStrictRange R D S (M ⨿ N) := by
  obtain ⟨M', hM', ⟨eM⟩⟩ := hM
  obtain ⟨N', hN', ⟨eN⟩⟩ := hN
  exact ⟨M' ⨿ N', hS M' N' hM' hN', ⟨coprod.mapIso eM eN⟩⟩

lemma dgModuleStrictRange_cone
    (hS : ∀ M N, S M → S N → ∀ f : M ⟶ N, S (moduleCone R D f))
    {M N : ModuleCategory R D} (hM : dgModuleStrictRange R D S M)
    (hN : dgModuleStrictRange R D S N) (f : M ⟶ N) :
    dgModuleStrictRange R D S (moduleCone R D f) := by
  obtain ⟨M', hM', ⟨eM⟩⟩ := hM
  obtain ⟨N', hN', ⟨eN⟩⟩ := hN
  let g := eM.hom ≫ f ≫ eN.inv
  exact ⟨moduleCone R D g, hS M' N' hM' hN' g,
    ⟨moduleConeIsoOfSquare R D g f eM eN (by simp [g])⟩⟩

lemma dgModuleStrictRange_countable
    (hS : ∀ N : ℕ → ModuleCategory R D, (∀ n, S (N n)) → S (∐ N))
    (M : ℕ → ModuleCategory R D) (hM : ∀ n, dgModuleStrictRange R D S (M n)) :
    dgModuleStrictRange R D S (∐ M) := by
  choose N hN e using hM
  exact ⟨∐ N, hS N hN, ⟨Sigma.mapIso (fun n => (e n).some)⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
