module

public import SerrePositivity.KST.Spectra.TriangleDiskFaces

/-!
概要：四辺で定数な正方形の写像を三角形の外側の辺へ制限する。
方針：境界の端点で検査し、零次元のパラメータを切断で除く。
規約：上側と下側で同じ向きの対角辺を使う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。正方形から相対三角形への制限。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (Y : PointedSimplicialSet.{u})
  (f : (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ Y.right)
  (hl : (boundary.{u} 1).ι ▷ (Δ[1] : SSet.{u}) ≫ f =
    toUnit ((boundary.{u} 1 : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) ≫ Y.hom)
  (hr : (Δ[1] : SSet.{u}) ◁ (boundary.{u} 1).ι ≫ f =
    toUnit ((Δ[1] : SSet.{u}) ⊗ (boundary.{u} 1 : SSet.{u})) ≫ Y.hom)

include hl in
/-- 概要：縦辺の端点パラメータを含む制限は定数。
方針：境界の各面との積を前合成する。
規約：端点の添字は任意。
使われ方：Goerss–Jardine I §7。縦辺の定数性の座標表示。 -/
theorem square_boundary_first (j : Fin 2) :
    stdSimplex.δ j ▷ (Δ[1] : SSet.{u}) ≫ f =
      toUnit ((Δ[0] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) ≫ Y.hom := by
  have h := congrArg (fun k => boundary.ι j ▷ (Δ[1] : SSet.{u}) ≫ k) hl
  simpa only [← comp_whiskerRight_assoc, boundary.ι_ι, comp_toUnit_assoc] using h

include hr in
/-- 概要：横辺の端点パラメータを含む制限は定数。
方針：第二変数の境界の各面を前合成する。
規約：端点の添字は任意。
使われ方：Goerss–Jardine I §7。横辺の定数性の座標表示。 -/
theorem square_boundary_second (j : Fin 2) :
    (Δ[1] : SSet.{u}) ◁ stdSimplex.δ j ≫ f =
      toUnit ((Δ[1] : SSet.{u}) ⊗ (Δ[0] : SSet.{u})) ≫ Y.hom := by
  have h := congrArg (fun k => (Δ[1] : SSet.{u}) ◁ boundary.ι j ≫ k) hr
  simpa only [← whiskerLeft_comp_assoc, boundary.ι_ι, comp_toUnit_assoc] using h

include hl in
/-- 概要：下側の零番目の面の制限は定数。
方針：縦の終辺の式に第二射影の切断を前合成する。
規約：零次元のパラメータを除く。
使われ方：Kerodon §3.2.3（Tag 00W3）。下側のホーンの消滅。 -/
theorem square_lower_face_zero :
    stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ f =
      toUnit (Δ[1] : SSet.{u}) ≫ Y.hom := by
  have h := square_boundary_first Y f hl (0 : Fin 2)
  rw [SquareTriangles.first_endpoint_zero, Category.assoc] at h
  have h' := congrArg (fun k =>
    lift (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) (𝟙 _) ≫ k) h
  simpa only [← Category.assoc, lift_snd, Category.id_comp, comp_toUnit, comp_toUnit_assoc] using h'

include hl in
/-- 概要：上側の最後の面の制限は定数。
方針：縦の始辺に第二射影の切断を前合成する。
規約：最後の面の添字は 2。
使われ方：Kerodon §3.2.3（Tag 00W3）。上側のホーンの消滅。 -/
theorem square_upper_face_last :
    stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ f =
      toUnit (Δ[1] : SSet.{u}) ≫ Y.hom := by
  have h := square_boundary_first Y f hl (1 : Fin 2)
  rw [SquareTriangles.first_endpoint_one, Category.assoc] at h
  have h' := congrArg (fun k =>
    lift (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) (𝟙 _) ≫ k) h
  simpa only [← Category.assoc, lift_snd, Category.id_comp, comp_toUnit, comp_toUnit_assoc] using h'

include hr in
/-- 概要：上側の零番目の面の制限は定数。
方針：横の終辺に第一射影の切断を前合成する。
規約：第一変数の区間は保つ。
使われ方：Kerodon §3.2.3（Tag 00W3）。上側のホーンの消滅。 -/
theorem square_upper_face_zero :
    stdSimplex.δ (0 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.upper ≫ f =
      toUnit (Δ[1] : SSet.{u}) ≫ Y.hom := by
  have h := square_boundary_second Y f hr (0 : Fin 2)
  rw [SquareTriangles.second_endpoint_zero, Category.assoc] at h
  have h' := congrArg (fun k =>
    lift (𝟙 _) (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) ≫ k) h
  simpa only [← Category.assoc, lift_fst, Category.id_comp, comp_toUnit, comp_toUnit_assoc] using h'

include hr in
/-- 概要：下側の最後の面の制限は定数。
方針：横の始辺に第一射影の切断を前合成する。
規約：最後の面の添字は 2。
使われ方：Kerodon §3.2.3（Tag 00W3）。下側のホーンの消滅。 -/
theorem square_lower_face_last :
    stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ f =
      toUnit (Δ[1] : SSet.{u}) ≫ Y.hom := by
  have h := square_boundary_second Y f hr (1 : Fin 2)
  rw [SquareTriangles.second_endpoint_one, Category.assoc] at h
  have h' := congrArg (fun k =>
    lift (𝟙 _) (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) ≫ k) h
  simpa only [← Category.assoc, lift_fst, Category.id_comp, comp_toUnit, comp_toUnit_assoc] using h'

end

end SerrePositivity.KST.Spectra
