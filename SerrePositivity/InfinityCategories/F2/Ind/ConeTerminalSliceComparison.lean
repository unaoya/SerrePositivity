module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTerminalSliceLift
public import SerrePositivity.InfinityCategories.F2.Ind.ConeApexTerminal
public import SerrePositivity.InfinityCategories.F2.Ind.RightAnodyneRelativeLiftIso

/-!
概要：恒等射で終わる終点 slice の持ち上げを、元の全余錐の標準持ち上げと比較する。
方針：右余錐頂点の right anodyne 性に、実相対持ち上げの同型を適用する。
規約：同じ元の全底図式を固定した空間で比較。使われ方：元の q の全変換の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 任意の右余錐の同じ頂点包含は right anodyne。 -/
lemma coneTip_rightAnodyne (A : SSet.{u}) :
    rightAnodyneExtensions (joinInr A (Δ[0] : SSet.{u})) := by
  have h := F1B.kanTerminalPoint_rightAnodyne (coneApex_isTerminalVertex A)
  have he : SSet.yonedaEquiv.symm (coneApex A) = joinInr A (Δ[0] : SSet.{u}) := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    have hz : (stdSimplex.obj₀Equiv.symm 0 : (Δ[0] : SSet.{u}) _⦋0⦌) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
      apply stdSimplex.ext
      intro j
      apply Fin.ext
      omega
    rw [coneApex, hz]
    simpa only [Category.id_comp] using
      (SSet.yonedaEquiv_comp (𝟙 (Δ[0] : SSet.{u})) (joinInr A Δ[0])).symm
  rwa [he] at h

variable {A X : SSet.{u}} [Quasicategory X] (x : X _⦋0⦌)
  (b : join A (Δ[0] : SSet.{u}) ⟶ X)
  (hb : joinInr A Δ[0] ≫ b = SSet.yonedaEquiv.symm x)
  (W : join A (Δ[0] : SSet.{u}) ⟶ sliceOver (SSet.yonedaEquiv.symm x))
  (hp : W ≫ sliceOverProjection (SSet.yonedaEquiv.symm x) = b)
  (ht : joinInr A Δ[0] ≫ W = SSet.yonedaEquiv.symm (sliceIdentityCone x))

/-- 指定の恒等終点で終わる同じ全余錐の二つの持ち上げは、底を固定して同型。 -/
def coneTerminalSliceRelativeIso :
    VertexIso
      (relativeFunctorVertex (sliceOverProjection (SSet.yonedaEquiv.symm x)) b W hp)
      (relativeFunctorVertex (sliceOverProjection (SSet.yonedaEquiv.symm x)) b
        (coneTerminalSliceLift x b hb) (coneTerminalSliceLift_projection x b hb)) :=
  rightAnodyneRelativeLiftIso (sliceOverProjection (SSet.yonedaEquiv.symm x)) b
    (joinInr A Δ[0]) (coneTip_rightAnodyne A) W (coneTerminalSliceLift x b hb)
    hp (coneTerminalSliceLift_projection x b hb) (ht.trans (coneTerminalSliceLift_tip x b hb).symm)

/-- 同じ底を固定したまま、元の族を元の全余錐の curry と比較する。 -/
def coneTerminalSliceBoundaryRelativeIso :
    VertexIso
      (relativeFunctorVertex (sliceOverProjection (SSet.yonedaEquiv.symm x))
        (joinInl A Δ[0] ≫ b) (joinInl A Δ[0] ≫ W) (by rw [Category.assoc, hp]))
      (relativeFunctorVertex (sliceOverProjection (SSet.yonedaEquiv.symm x))
        (joinInl A Δ[0] ≫ b) (sliceOverCurry b hb) (sliceOverCurry_projection b hb)) := by
  have h := VertexIso.map (coneTerminalSliceRelativeIso x b hb W hp ht)
    (relativeFunctorPre (sliceOverProjection (SSet.yonedaEquiv.symm x)) b (joinInl A Δ[0]))
  simpa only [relativeFunctorPre_vertex, coneTerminalSliceLift_old] using h

end SerrePositivity.InfinityCategories.F2.Ind
