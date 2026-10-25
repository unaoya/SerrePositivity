module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.YonedaHomNaturality
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransCommonIso
/-!
概要：代表からの全 Hom と評価の dg Yoneda 比較を共通宇宙の全 nerve 関手同型へ移す。
方針：全次数自然な厳密 dg 自然変換と同じ閉同型成分を使う。
規約：対象ごとの写像空間同型だけでなく、全 coherent 図式で前合成できる比較。
使われ方：c2 の native Hom と評価の交換の準備。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve Opposite
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 鎖同型を同じ閉次数零成分の同型として読む。 -/
def dgBarCompactComplex_closedIso {X Y : Complex R} (e : X ≅ Y) :
    ForgetEnrichment.of (Complex R) X ≅ ForgetEnrichment.of (Complex R) Y where
  hom := (complexClosedHomEquiv R _ _).symm e.hom
  inv := (complexClosedHomEquiv R _ _).symm e.inv
  hom_inv_id := by
    apply (closedToComplex R).map_injective
    change complexClosedHomEquiv R _ _ (_ ≫ _) = complexClosedHomEquiv R _ _ (𝟙 _)
    rw [complexClosedHomEquiv_comp, complexClosedHomEquiv_id]
    change complexClosedHomEquiv R X Y ((complexClosedHomEquiv R X Y).symm e.hom) ≫
      complexClosedHomEquiv R Y X ((complexClosedHomEquiv R Y X).symm e.inv) = 𝟙 X
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact e.hom_inv_id
  inv_hom_id := by
    apply (closedToComplex R).map_injective
    change complexClosedHomEquiv R _ _ (_ ≫ _) = complexClosedHomEquiv R _ _ (𝟙 _)
    rw [complexClosedHomEquiv_comp, complexClosedHomEquiv_id]
    change complexClosedHomEquiv R Y X ((complexClosedHomEquiv R Y X).symm e.inv) ≫
      complexClosedHomEquiv R X Y ((complexClosedHomEquiv R X Y).symm e.hom) = 𝟙 Y
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact e.inv_hom_id

/-- 元の dg Yoneda 鎖同型を、同じ成分の閉次数零同型として読む。 -/
def dgBarCompactYoneda_closedIso (x : D) (M : RightModule R D) :
    ForgetEnrichment.of (Complex R) ((leftRepresentable R (representable R x)).obj M) ≅
      ForgetEnrichment.of (Complex R) ((moduleEvaluationDG R D x).obj M) :=
  dgBarCompactComplex_closedIso R (dgYonedaIso R x M)

/-- 独立の対象宇宙を許す、全 Hom と評価の共通宇宙 nerve 関手同型。 -/
def dgBarCompactYoneda_nerveIso (x : D) :
    FunctorIso
      (dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
        (leftRepresentable R (representable R x)))
      (dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
        (moduleEvaluationDG R D x)) := by
  apply dgStrictNatTransCommonFunctorIso (dgBarCompactYoneda_strict R D x)
    (dgBarCompactYoneda_closedIso R D x)
  intro M
  change cycleFromUnit (homComplex R (moduleHom R D (representable R x) M)
      (M.obj (op x))) (closedMap R (dgYonedaIso R x M).hom) =
    cycleFromUnit (homComplex R (moduleHom R D (representable R x) M)
      (M.obj (op x))) ((complexClosedHomEquiv R _ _).symm (dgYonedaIso R x M).hom)
  rfl

end SerrePositivity.InfinityCategories
