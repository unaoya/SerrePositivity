module
public import SerrePositivity.DifferentialGraded.Module.Triangulated
/-!
概要：加群のホモトピー同型による端点変更を、同じ標準 cone の同型へ延長する。
方針：商関手の充満性で実閉射を選び、標準 distinguished triangle の二頂点比較を使う。
規約：端点の同型はホモトピー圏に置き、実加群の厳密同型を仮定しない。
使われ方：κ-small 提示の同時精密化で、代表化後の実閉射と cone を回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Pretriangulated
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {M N M' N' : ModuleCategory R D}

lemma moduleHomotopyCone_transport_endpoints (f : M ⟶ N)
    (eM : (moduleToHomotopy R D).obj M ≅ (moduleToHomotopy R D).obj M')
    (eN : (moduleToHomotopy R D).obj N ≅ (moduleToHomotopy R D).obj N') :
    ∃ g : M' ⟶ N', Nonempty ((moduleToHomotopy R D).obj (moduleCone R D f) ≅
      (moduleToHomotopy R D).obj (moduleCone R D g)) := by
  let K := moduleToHomotopy R D
  obtain ⟨g, hg⟩ := K.map_surjective (eM.inv ≫ K.map f ≫ eN.hom)
  have hcomm : K.map f ≫ eN.hom = eM.hom ≫ K.map g := by
    rw [hg]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact ⟨g, ⟨(Triangle.π₃).mapIso (isoTriangleOfIso₁₂
    (moduleHomotopyConeTriangle R D f) (moduleHomotopyConeTriangle R D g)
    (moduleHomotopyConeTriangle_distinguished R D f)
    (moduleHomotopyConeTriangle_distinguished R D g) eM eN hcomm)⟩⟩

end SerrePositivity.DifferentialGraded
