module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialRestrictionHomNaturality

/-!
概要：比較辺による合成三角形の終点側を、元の始対象の Hom 比較で全単体において計算する。
方針：図式表示の等号による移送を uncurry で消し、比較 span の後合成を一段にまとめる。
規約：点ごとの Hom の一致ではなく実際の余錐族の等式。使われ方：Hom の前合成の正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 固定図式の等号による表示変更は、余錐族の uncurry を変えない。 -/
lemma sliceUnderUncurry_eqToHom {K T X : SSet.{u}} {p q : K ⟶ X}
    (h : p = q) (a : T ⟶ sliceUnder p) :
    sliceUnderUncurry (a ≫ eqToHom (congrArg sliceUnder h)) = sliceUnderUncurry a := by
  cases h
  rw [eqToHom_refl, Category.comp_id]

variable {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
  (r : E ⟶ F) (hr : r ≫ q = p) (d : E _⦋0⦌) (hd : IsInitialVertex d)
  {c : F _⦋0⦌} (e : F.Edge c (r.app (Opposite.op ⦋0⦌) d)) (y : B _⦋0⦌)

include hr in
/-- 元の始点の底での像と、比較辺の終点の底での像は同じ点図式。 -/
lemma initialRestrictionEdgeBase_eq :
    SSet.yonedaEquiv.symm d ≫ p =
      stdSimplex.δ (0 : Fin 2) ≫ (SSet.yonedaEquiv.symm e.edge ≫ q) := by
  rw [← Category.assoc, e.δ_zero_yonedaEquiv_symm]
  exact leftFibrationInitialBaseDiagram_eq p q r hr d (r.app (Opposite.op ⦋0⦌) d) rfl

/-- 全空間の族の底への射影は、元の比較 span の底の射影を点図式の等号で移したもの。 -/
lemma initialRestrictionEdgeFamily_base :
    initialRestrictionEdgeFamily p q r hr d hd e y ≫
        sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm e.edge) q =
      (leftFibrationInitialSection p d hd y ≫ leftFibrationInitialProjection p d y ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm d ≫ p)) y) ≫
          eqToHom (congrArg sliceUnder (initialRestrictionEdgeBase_eq p q r hr d e)) := by
  let s := leftFibrationInitialSection p d hd y
  let z := r.app (Opposite.op ⦋0⦌) d
  let I := vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm d) ≫ p) y
  have hm : (s ≫ leftFibrationInitialTotalMap p q r hr d z rfl y) ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm z) ≫ q) y =
      (s ≫ I) ≫ stableCoslicePostcomp (SSet.yonedaEquiv.symm d) r
        (SSet.yonedaEquiv.symm z) (SSet.yonedaEquiv_symm_comp d r) := by
    rw [Category.assoc, leftFibrationInitialTotalMap, vertexFiberMap_ι, ← Category.assoc]
  have ha : sliceUnderUncurry (initialRestrictionEdgeFamily p q r hr d hd e y) =
      sliceUnderUncurry (s ≫ I) ≫ r := by
    change sliceUnderUncurry
      (((s ≫ leftFibrationInitialTotalMap p q r hr d z rfl y) ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm z) ≫ q) y) ≫
        eqToHom (congrArg sliceUnder e.δ_zero_yonedaEquiv_symm.symm)) = _
    rw [sliceUnderUncurry_eqToHom e.δ_zero_yonedaEquiv_symm.symm, hm,
      stableCoslicePostcomp_uncurry]
  have hp : (s ≫ leftFibrationInitialProjection p d y) ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm d ≫ p)) y =
      (s ≫ I) ≫ sliceUnderPostcomp (SSet.yonedaEquiv.symm d) p := by
    rw [Category.assoc, leftFibrationInitialProjection, vertexFiberMap_ι, ← Category.assoc]
  apply sliceUnderUncurry_injective
  rw [sliceUnderUncurry_postcomp, ha, Category.assoc, hr,
    sliceUnderUncurry_eqToHom (initialRestrictionEdgeBase_eq p q r hr d e)]
  change _ = sliceUnderUncurry ((s ≫ leftFibrationInitialProjection p d y) ≫
    vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm d ≫ p)) y)
  rw [hp, sliceUnderUncurry_postcomp]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
