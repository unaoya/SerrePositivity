module
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.RepresentativeImage
public import SerrePositivity.InfinityCategories.Derived.KappaCovers.TelescopeSplitting
public import SerrePositivity.DifferentialGraded.Module.HomotopyCoproductUniversal

/-!
概要：同じ選択代表系の K(D) 内の本質像は可算直和と retract で閉じる。
方針：実直和の普遍性を比較し、指定 telescope cone の分裂を三角的対象条件に適用する。
規約：集合への厳密所属とホモトピー同型による被覆を区別する。
使われ方：D-8 d の retract 段を同じ小さい代表族に戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) (hreg : κ.IsRegular)
include hκ hreg

lemma dgKappaCoversImage_countable (X : ℕ → ModuleHomotopyCategory R D)
    (hX : ∀ n, dgKappaCoversImage R D κ (X n)) :
    dgKappaCoversImage R D κ (∐ X) := by
  choose M hM e using fun n => (dgKappaCoversImage_iff R D κ (X n)).mp (hX n)
  let i (n : ℕ) := (e n).some
  apply (dgKappaCoversImage_iff R D κ (∐ X)).mpr
  refine ⟨∐ M, dgKappaClosedProjectiveObjects_countableClosed R D hκ hreg M hM, ⟨?_⟩⟩
  exact (moduleHomotopyCofanIsColimit R D M).coconePointUniqueUpToIso
    (coproductIsCoproduct (fun n => (moduleToHomotopy R D).obj (M n))) ≪≫ Sigma.mapIso i

lemma dgKappaCoversImage_of_retract {X Y : ModuleHomotopyCategory R D}
    (r : Retract X Y) (hY : dgKappaCoversImage R D κ Y) :
    dgKappaCoversImage R D κ X := by
  let := dgKappaCoversImage_isTriangulated R D κ hκ hreg
  apply triangulatedProperty_of_retract_countable (dgKappaCoversImage R D κ) ?_ r hY
  intro Z hZ
  exact dgKappaCoversImage_countable R D hκ hreg (fun _ => Z) (fun _ => hZ)

/-- 同じ選択族の一対象の K(D) 内の retract は、同じ族で同型まで代表される。 -/
lemma dgKappaClosedProjectiveObjects_homotopyRetractCovers
    {X : ModuleHomotopyCategory R D} {M : ModuleCategory R D}
    (hM : dgKappaClosedProjectiveObjects R D κ M)
    (r : Retract X ((moduleToHomotopy R D).obj M)) :
    ∃ N : ModuleCategory R D, dgKappaClosedProjectiveObjects R D κ N ∧
      Nonempty ((moduleToHomotopy R D).obj N ≅ X) := by
  apply (dgKappaCoversImage_iff R D κ X).mp
  apply dgKappaCoversImage_of_retract R D hκ hreg r
  exact (dgKappaCoversImage_iff R D κ _).mpr ⟨M, hM, ⟨Iso.refl _⟩⟩

end SerrePositivity.InfinityCategories
