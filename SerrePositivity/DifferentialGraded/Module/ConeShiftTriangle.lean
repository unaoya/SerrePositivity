module
public import SerrePositivity.DifferentialGraded.Module.ConeShiftTriangleOrdinary
public import SerrePositivity.DifferentialGraded.Module.TriangleShiftMap
public import SerrePositivity.DifferentialGraded.Module.DistinguishedTriangles

/-! # K(D)の標準cone三角形の整数shift比較 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 商関手のshift比較を含む標準cone三角形のshift同型。 -/
def moduleHomotopyConeShiftIso (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :=
  triangleShiftMapIso (moduleToHomotopy A D) s (moduleConeTriangle A D f)
    (moduleConeTriangle A D (moduleShiftMap A D s f)) (moduleConeTriangleShiftIso A D s f)

lemma moduleDistinguished_ofConeIso {M N : ModuleCategory A D} (f : M ⟶ N)
    (T : Triangle (ModuleHomotopyCategory A D))
    (e : T ≅ (moduleToHomotopy A D).mapTriangle.obj (moduleConeTriangle A D f)) :
    T ∈ moduleDistinguishedTriangles A D := ⟨M, N, f, ⟨e⟩⟩

-- 豊穣coneと商shiftの型変換を含む、この証明のカーネル検査に上限を指定する。
set_option maxHeartbeats 800000 in
lemma moduleDistinguished_shift (T : Triangle (ModuleHomotopyCategory A D))
    (hT : T ∈ moduleDistinguishedTriangles A D) (s : ℤ) :
    (Triangle.shiftFunctor (ModuleHomotopyCategory A D) s).obj T ∈ moduleDistinguishedTriangles A D := by
  change ∃ (M N : ModuleCategory A D) (f : M ⟶ N),
    Nonempty (T ≅ (moduleToHomotopy A D).mapTriangle.obj (moduleConeTriangle A D f)) at hT
  obtain ⟨M, N, f, ⟨e⟩⟩ := hT
  let e' := triangleShiftIsoTrans s T
    ((moduleToHomotopy A D).mapTriangle.obj (moduleConeTriangle A D f))
    ((moduleToHomotopy A D).mapTriangle.obj (moduleConeTriangle A D (moduleShiftMap A D s f)))
    e (moduleHomotopyConeShiftIso A D s f)
  exact moduleDistinguished_ofConeIso A D (moduleShiftMap A D s f) _ e'
end SerrePositivity.DifferentialGraded
