module
public import SerrePositivity.InfinityCategories.Derived.DGNerveCommonMap
public import SerrePositivity.InfinityCategories.Core.UniverseSquareHom
/-!
概要：共通宇宙の dg nerve 写像が標準単体と四角形の宇宙比較に整合する。
方針：標準単体上の写像を Yoneda で評価し、四角形の二セルを比較する。
規約：元の次数付き成分と全単体作用を保持する。
使われ方：混在宇宙の標準 cone 四角形を完全性へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} {E : Type w}
  [DGCategory R D] [DGCategory R E]

lemma dgNerveCommonMap_simplex (F : DGFunctor R D E) {n : ℕ} (s : Simplex R D n) :
    uliftSimplexHomEquiv.{max u v, max u v w t} (dgNerve R D) n
        (SSet.yonedaEquiv.symm s) ≫ dgNerveCommonMap.{u, v, w, t} F =
      uliftSimplexHomEquiv.{max u w, max u v w t} (dgNerve R E) n
        (SSet.yonedaEquiv.symm (s.map F)) := by
  have hd : uliftSimplexHomEquiv.{max u v, max u v w t} (dgNerve R D) n
      (SSet.yonedaEquiv.symm s) = SSet.yonedaEquiv.symm (ULift.up s) :=
    HomotopyLimits.uliftYonedaMap.{max u v, max u v w t} (X := dgNerve R D) s
  have he : uliftSimplexHomEquiv.{max u w, max u v w t} (dgNerve R E) n
      (SSet.yonedaEquiv.symm (s.map F)) = SSet.yonedaEquiv.symm (ULift.up (s.map F)) :=
    HomotopyLimits.uliftYonedaMap.{max u w, max u v w t}
      (X := dgNerve R E) (s.map F)
  rw [hd, he, SSet.yonedaEquiv_symm_comp]
  rfl

lemma uliftSquare_triangle {X : SSet.{u}} (s : Δ[1] ⊗ Δ[1] ⟶ X) (i : Fin 2) :
    squareTriangle i ≫ uliftSquare.{u, v} s =
      uliftSimplexHomEquiv.{u, v} X 2 (squareTriangle i ≫ s) := by
  ext n x
  fin_cases i <;> rfl

end SerrePositivity.InfinityCategories
