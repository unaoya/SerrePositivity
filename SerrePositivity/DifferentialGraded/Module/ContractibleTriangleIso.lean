module
public import SerrePositivity.DifferentialGraded.Module.ConeContractible

/-! # 自明三角形と恒等cone三角形の同型 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated Limits ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 第三対象の収縮を使い、恒等cone三角形を自明三角形と比較する。 -/
def moduleHomotopyIdentityConeTriangleIso (M : ModuleCategory A D) :
    contractibleTriangle ((moduleToHomotopy A D).obj M) ≅
      moduleHomotopyConeTriangle A D (𝟙 M) := by
  let Q := moduleToHomotopy A D
  let T := moduleHomotopyConeTriangle A D (𝟙 M)
  let h := moduleConeId_isZero A D M
  let e : (0 : ModuleHomotopyCategory A D) ≅ Q.obj (moduleCone A D (𝟙 M)) := h.isoZero.symm
  refine Triangle.isoMk (contractibleTriangle (Q.obj M)) T
    (Iso.refl (Q.obj M)) (Iso.refl (Q.obj M)) e ?_ ?_ ?_
  · change (𝟙 (Q.obj M)) ≫ 𝟙 _ = 𝟙 _ ≫ Q.map (𝟙 M)
    rw [Q.map_id, Category.id_comp]
  · exact h.eq_of_tgt _ _
  · exact (isZero_zero (ModuleHomotopyCategory A D)).eq_of_src _ _

end SerrePositivity.DifferentialGraded
