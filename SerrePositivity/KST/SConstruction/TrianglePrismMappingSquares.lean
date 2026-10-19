module
public import SerrePositivity.KST.SConstruction.TrianglePrismMappingImages

/-! # 元の合成 prism の同じ Hom 内の三つの実正方形
概要：元の三単体の Hom 正方形を共通両端へ移し、四辺と二つの共有面を厳密に保持する。
方針：元の tetrahedronTrace の四面の式と、共有する二単体の等式を使う。
規約：元の prism の Hom 正方形を選び直さず、対象の表示だけを照合する。
使われ方：元の合成射の適合区間と二本の入力射の適合区間の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open Spectra.CoherentPathCoordinates
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  (Q : (Δ[2] : SSet.{max u v}) ⊗ Δ[1] ⟶ SimplicialNerve C)

/-- 元の合成 prism の三つの正方形を、同じ元の始点・終点の Hom へ表示する。 -/
def trianglePrismMappingSquare (q : Fin 3) : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
    SimplicialCategory.sHom (trianglePrismSource Q) (trianglePrismTarget Q) :=
  tetrahedronTrace (trianglePrismImage Q q) ≫ eqToHom (trianglePrismImage_hom Q q)

/-- 第一座標零は、元の三単体の一番面の同じ Hom 区間。 -/
lemma trianglePrismMappingSquare_skip_first (q : Fin 3) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
      trianglePrismMappingSquare Q q =
      triangleTrace ((SimplicialNerve C).δ 1 (trianglePrismImage Q q)) ≫
        eqToHom (trianglePrismImage_hom Q q) := by
  rw [trianglePrismMappingSquare, ← Category.assoc, tetrahedronTrace_skipFirst]

/-- 第二座標零は、元の三単体の二番面の同じ Hom 区間。 -/
lemma trianglePrismMappingSquare_skip_second (q : Fin 3) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
      trianglePrismMappingSquare Q q =
      triangleTrace ((SimplicialNerve C).δ 2 (trianglePrismImage Q q)) ≫
        eqToHom (trianglePrismImage_hom Q q) := by
  rw [trianglePrismMappingSquare, ← Category.assoc, tetrahedronTrace_skipSecond]

/-- 第一座標一は、元の最初の辺と零番面の区間の実合成。 -/
lemma trianglePrismMappingSquare_include_first (q : Fin 3) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
      trianglePrismMappingSquare Q q =
      lift (tetrahedronInitialTrace (trianglePrismImage Q q))
        (triangleTrace ((SimplicialNerve C).δ 0 (trianglePrismImage Q q))) ≫
          eComp SSet ((trianglePrismImage Q q).obj (.mk (ULift.up 0)))
            ((trianglePrismImage Q q).obj (.mk (ULift.up 1)))
            ((trianglePrismImage Q q).obj (.mk (ULift.up 3))) ≫
          eqToHom (trianglePrismImage_hom Q q) := by
  rw [trianglePrismMappingSquare, ← Category.assoc, tetrahedronTrace_includeFirst]
  exact Category.assoc _ _ _

/-- 第二座標一は、元の三番面の区間と最後の辺の実合成。 -/
lemma trianglePrismMappingSquare_include_second (q : Fin 3) :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
      trianglePrismMappingSquare Q q =
      lift (triangleTrace ((SimplicialNerve C).δ 3 (trianglePrismImage Q q)))
        (tetrahedronFinalTrace (trianglePrismImage Q q)) ≫
          eComp SSet ((trianglePrismImage Q q).obj (.mk (ULift.up 0)))
            ((trianglePrismImage Q q).obj (.mk (ULift.up 2)))
            ((trianglePrismImage Q q).obj (.mk (ULift.up 3))) ≫
          eqToHom (trianglePrismImage_hom Q q) := by
  rw [trianglePrismMappingSquare, ← Category.assoc, tetrahedronTrace_includeSecond]
  exact Category.assoc _ _ _

/-- 最初と中央の実正方形は、元の同じ共有区間で厳密に貼り合う。 -/
lemma trianglePrismMappingSquare_shared_first :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        trianglePrismMappingSquare Q 0 =
      lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        trianglePrismMappingSquare Q 1 := by
  rw [trianglePrismMappingSquare_skip_first, trianglePrismMappingSquare_skip_first]
  exact triangleTrace_transport (trianglePrismImage_shared_first Q) _ _

/-- 中央と最後の実正方形も、元の同じ共有区間で厳密に貼り合う。 -/
lemma trianglePrismMappingSquare_shared_second :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
        trianglePrismMappingSquare Q 1 =
      lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
        trianglePrismMappingSquare Q 2 := by
  rw [trianglePrismMappingSquare_skip_second, trianglePrismMappingSquare_skip_second]
  exact triangleTrace_transport (trianglePrismImage_shared_second Q) _ _

end SerrePositivity.KST.SConstruction
