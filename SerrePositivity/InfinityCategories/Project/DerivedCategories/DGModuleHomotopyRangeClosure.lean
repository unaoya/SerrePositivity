module
public import SerrePositivity.DifferentialGraded.Module.MaurerCartanTriangulated
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
/-!
概要：実加群の演算で閉じた族を、ホモトピー同型による飽和へ拡張する。
方針：閉射を充満な商関手で移し、標準 cone と余積・shift の比較を使う。
規約：全同型コピーを小さい対象集合へ追加しない。これは対象の性質としてのみ使う。
使われ方：c′ の seed 延長に対する超限閉包の帰納的不変条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory CategoryTheory.Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (S : Set (ModuleCategory R D))

def dgModuleHomotopyRange (M : ModuleCategory R D) : Prop :=
  ∃ N, S N ∧ Nonempty ((moduleToHomotopy R D).obj N ≅ (moduleToHomotopy R D).obj M)

lemma dgModuleHomotopyRange_of_mem {M : ModuleCategory R D} (hM : S M) :
    dgModuleHomotopyRange R D S M := ⟨M, hM, ⟨Iso.refl _⟩⟩

lemma dgModuleHomotopyRange_of_iso {M N : ModuleCategory R D}
    (e : (moduleToHomotopy R D).obj M ≅ (moduleToHomotopy R D).obj N)
    (hM : dgModuleHomotopyRange R D S M) : dgModuleHomotopyRange R D S N := by
  obtain ⟨L, hL, ⟨h⟩⟩ := hM
  exact ⟨L, hL, ⟨h ≪≫ e⟩⟩

lemma dgModuleHomotopyRange_shift
    (hS : ∀ M, S M → ∀ s : ℤ, S (M⟦s⟧))
    {M : ModuleCategory R D} (hM : dgModuleHomotopyRange R D S M) (s : ℤ) :
    dgModuleHomotopyRange R D S (M⟦s⟧) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := hM
  let K := moduleToHomotopy R D
  exact ⟨N⟦s⟧, hS N hN s, ⟨(K.commShiftIso s).app N ≪≫
    (shiftFunctor (ModuleHomotopyCategory R D) s).mapIso e ≪≫
    ((K.commShiftIso s).app M).symm⟩⟩

lemma dgModuleHomotopyRange_cone
    (hS : ∀ M N, S M → S N → ∀ f : M ⟶ N, S (moduleCone R D f))
    {M N : ModuleCategory R D} (hM : dgModuleHomotopyRange R D S M)
    (hN : dgModuleHomotopyRange R D S N) (f : M ⟶ N) :
    dgModuleHomotopyRange R D S (moduleCone R D f) := by
  obtain ⟨M', hM', ⟨eM⟩⟩ := hM
  obtain ⟨N', hN', ⟨eN⟩⟩ := hN
  obtain ⟨g, ⟨e⟩⟩ := moduleHomotopyCone_transport_endpoints R D f eM.symm eN.symm
  exact ⟨moduleCone R D g, hS M' N' hM' hN' g, ⟨e.symm⟩⟩

lemma dgModuleHomotopyRange_binary
    (hS : ∀ M N, S M → S N → S (M ⨿ N))
    {M N : ModuleCategory R D} (hM : dgModuleHomotopyRange R D S M)
    (hN : dgModuleHomotopyRange R D S N) : dgModuleHomotopyRange R D S (M ⨿ N) := by
  obtain ⟨M', hM', ⟨eM⟩⟩ := hM
  obtain ⟨N', hN', ⟨eN⟩⟩ := hN
  let K := moduleToHomotopy R D
  exact ⟨M' ⨿ N', hS M' N' hM' hN', ⟨(PreservesColimitPair.iso K M' N').symm ≪≫
    coprod.mapIso eM eN ≪≫ PreservesColimitPair.iso K M N⟩⟩

lemma dgModuleHomotopyRange_coproduct {J : Type w} [Small.{u} J]
    (hS : ∀ N : J → ModuleCategory R D, (∀ j, S (N j)) → S (∐ N))
    (M : J → ModuleCategory R D) (hM : ∀ j, dgModuleHomotopyRange R D S (M j)) :
    dgModuleHomotopyRange R D S (∐ M) := by
  choose N hN e using hM
  let K := moduleToHomotopy R D
  exact ⟨∐ N, hS N hN, ⟨PreservesCoproduct.iso K N ≪≫
    Sigma.mapIso (fun j => (e j).some) ≪≫ (PreservesCoproduct.iso K M).symm⟩⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
