module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGPretriangulated
public import SerrePositivity.DifferentialGraded.Verdier.Derived

/-! # K(D) における有限 cell の三角的生成性

概要：有限 cell の K(D) の像は代表加群を含む最小の同型で閉じた三角的対象条件。
方針：零・シフト・有限和・cone・同型からなる有限操作木で帰納する。
規約：retract は加えない。使われ方：前三角性と tria の代表対象との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits Pretriangulated DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : ObjectProperty (ModuleHomotopyCategory A D))
variable [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

/-- K(D) の三角的対象条件は実有限和の像で閉じる。 -/
lemma dgModuleHomotopyBiprod_mem {M N : ModuleCategory A D}
    (hM : P ((moduleToHomotopy A D).obj M))
    (hN : P ((moduleToHomotopy A D).obj N)) :
    P ((moduleToHomotopy A D).obj (moduleBiprod A D M N)) := by
  have : PreservesBinaryBiproducts (moduleToHomotopy A D) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have h := P.ext_of_isTriangulatedClosed₂'
    (binaryBiproductTriangle ((moduleToHomotopy A D).obj M) ((moduleToHomotopy A D).obj N))
    (binaryBiproductTriangle_distinguished _ _) hM hN
  rw [ObjectProperty.isoClosure_eq_self] at h
  exact P.prop_of_iso
    ((moduleToHomotopy A D).mapIso (moduleBiprodIso A D M N) ≪≫
      (moduleToHomotopy A D).mapBiprod M N).symm h

/-- 有限操作木の全節点は生成元を含む三角的対象条件を満たす。 -/
lemma dgModuleFiniteCellCode_mem_homotopy {S : Set D}
    (hgen : ∀ x ∈ S, P ((moduleToHomotopy A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x))))
    {M : ModuleCategory A D} (c : ModuleFiniteCellCode A D S M) :
    P ((moduleToHomotopy A D).obj M) := by
  induction c with
  | zero => exact P.prop_of_isZero ((moduleToHomotopy A D).map_isZero (moduleZero_isZero A D))
  | generator x hx => exact hgen x hx
  | @shift M s c ih =>
    exact P.prop_of_iso (((moduleToHomotopy A D).commShiftIso s).app M).symm
      (P.le_shift s _ ih)
  | sum c d ihc ihd => exact dgModuleHomotopyBiprod_mem A D P ihc ihd
  | cone c d f ihc ihd =>
    exact P.ext_of_isTriangulatedClosed₃ (moduleHomotopyConeTriangle A D f)
      (moduleHomotopyConeTriangle_distinguished A D f) ihc ihd
  | iso c e ih => exact P.prop_of_iso ((moduleToHomotopy A D).mapIso e) ih

/-- 有限 cell のホモトピー本質像の包含は生成元だけで判定できる。 -/
lemma homotopyFiniteCellOver_le_iff_generators (S : Set D) :
    homotopyFiniteCellOver A D S ≤ P ↔ ∀ x ∈ S, P ((moduleToHomotopy A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x))) := by
  constructor
  · intro h x hx
    exact h _ ((moduleFiniteCellOver A D S).prop_map_obj (moduleToHomotopy A D)
      (moduleFiniteCellOver_representable A D x hx))
  · intro h X hX
    obtain ⟨M, ⟨c⟩, ⟨e⟩⟩ := hX
    exact P.prop_of_iso e (dgModuleFiniteCellCode_mem_homotopy A D P h c)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
