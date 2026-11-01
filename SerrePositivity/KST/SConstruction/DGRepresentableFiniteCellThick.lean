module
public import SerrePositivity.DifferentialGraded.Endomorphism.Scalar.EnhancementComparison
public import SerrePositivity.DifferentialGraded.Perfect.Basic

/-! # 指定代表加群の有限 cell とホモトピー thick 閉包
概要：指定代表加群一つからの有限 cell を、同じ代表のホモトピー thick 閉包へ送る。
方針：元の有限 cell 符号を shift・直和・円錐・同型について帰納する。
規約：既存の D の有限 cell と三角形を使う。使われ方：具体的商 End の生成条件。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits Pretriangulated DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (b : D)
local notation "H" => moduleToHomotopy R D
local notation "P" => endomorphismThickClosure R D (representable R b)

/-- 元の加群直和のホモトピー像は、両成分と同じ thick 閉包に入る。 -/
lemma dgRepresentableThick_biprod {M N : ModuleCategory R D}
    (hM : (P) ((H).obj M)) (hN : (P) ((H).obj N)) :
    (P) ((H).obj (moduleBiprod R D M N)) := by
  have : PreservesBinaryBiproducts (H) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have h := (P).ext_of_isTriangulatedClosed₂'
    (binaryBiproductTriangle ((H).obj M) ((H).obj N))
    (binaryBiproductTriangle_distinguished _ _) hM hN
  rw [ObjectProperty.isoClosure_eq_self] at h
  exact (P).prop_of_iso
    ((H).mapIso (moduleBiprodIso R D M N) ≪≫ (H).mapBiprod M N).symm h

/-- 指定代表一つからの元の有限 cell 符号は、同じホモトピー thick 閉包に入る。 -/
lemma dgRepresentableThick_of_finiteCell {M : ModuleCategory R D}
    (c : ModuleFiniteCellCode R D {b} M) : (P) ((H).obj M) := by
  induction c with
  | zero => exact (P).prop_of_isZero ((H).map_isZero (moduleZero_isZero R D))
  | generator x hx =>
    have hx : x = b := Set.mem_singleton_iff.mp hx
    subst x
    exact endomorphismThickClosure.generator
  | shift s c ih =>
    exact (P).prop_of_iso (((H).commShiftIso s).app _).symm ((P).le_shift s _ ih)
  | sum c d ihc ihd => exact dgRepresentableThick_biprod R D b ihc ihd
  | cone c d f ihc ihd =>
    exact (P).ext_of_isTriangulatedClosed₃ _
      (moduleHomotopyConeTriangle_distinguished R D f) ihc ihd
  | iso c e ih => exact (P).prop_of_iso ((H).mapIso e) ih

end SerrePositivity.KST.SConstruction
