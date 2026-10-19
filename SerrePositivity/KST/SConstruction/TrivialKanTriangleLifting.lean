module
public import SerrePositivity.KST.SConstruction.TriangleBoundaryMaps

/-! # 全三辺を固定した指定三角形の持ち上げ
概要：全単射 RLP を持つ射に沿い、三辺と基底の全二単体を厳密に保って持ち上げる。
方針：元の三辺を全境界へ貼り、境界包含に対する一回の持ち上げを使う。
規約：三辺のうち一つを選び直すホーン充填ではなく、全境界を固定する。
使われ方：anodyne なパラメータ包含に沿う、元の比較三角形の相対延長。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 全三辺と指定された基底の全二単体を保持する、実三角形の持ち上げ。 -/
def trivialKanTriangleLift {E B : SSet.{u}} (q : E ⟶ B)
    (hq : (MorphismProperty.monomorphisms SSet.{u}).rlp q)
    {a b c : E _⦋0⦌} (f : E.Edge a b) (g : E.Edge b c) (h : E.Edge a c)
    (t : SSet.Edge.CompStruct (f.map q) (g.map q) (h.map q)) :
    {s : SSet.Edge.CompStruct f g h //
      q.app (Opposite.op ⦋2⦌) s.simplex = t.simplex} := by
  letI : HasLiftingProperty (boundary.{u} 2).ι q := hq _ inferInstance
  let sq : CommSq (triangleBoundaryMap f g h) (boundary 2).ι q
      (SSet.yonedaEquiv.symm t.simplex) := ⟨by
    apply boundary.hom_ext
    intro i
    rw [← Category.assoc, triangleBoundaryMap_face, boundary.ι_ι_assoc]
    fin_cases i
    · change SSet.yonedaEquiv.symm g.edge ≫ q =
        stdSimplex.δ 0 ≫ SSet.yonedaEquiv.symm t.simplex
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, t.d₀, SSet.yonedaEquiv_symm_comp]
      rfl
    · change SSet.yonedaEquiv.symm h.edge ≫ q =
        stdSimplex.δ 1 ≫ SSet.yonedaEquiv.symm t.simplex
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, t.d₁, SSet.yonedaEquiv_symm_comp]
      rfl
    · change SSet.yonedaEquiv.symm f.edge ≫ q =
        stdSimplex.δ 2 ≫ SSet.yonedaEquiv.symm t.simplex
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, t.d₂, SSet.yonedaEquiv_symm_comp]
      rfl⟩
  have hs (i : Fin 3) : stdSimplex.δ i ≫ sq.lift = triangleBoundaryFaces f g h i := by
    rw [← boundary.ι_ι_assoc, sq.fac_left, triangleBoundaryMap_face]
  refine ⟨SSet.Edge.CompStruct.mk (SSet.yonedaEquiv sq.lift) ?_ ?_ ?_, ?_⟩
  · rw [← stdSimplex.yonedaEquiv_δ_comp, hs 2]
    exact SSet.yonedaEquiv.apply_symm_apply _
  · rw [← stdSimplex.yonedaEquiv_δ_comp, hs 0]
    exact SSet.yonedaEquiv.apply_symm_apply _
  · rw [← stdSimplex.yonedaEquiv_δ_comp, hs 1]
    exact SSet.yonedaEquiv.apply_symm_apply _
  · change q.app (Opposite.op ⦋2⦌) (SSet.yonedaEquiv sq.lift) = t.simplex
    rw [← SSet.yonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]

end SerrePositivity.KST.SConstruction
