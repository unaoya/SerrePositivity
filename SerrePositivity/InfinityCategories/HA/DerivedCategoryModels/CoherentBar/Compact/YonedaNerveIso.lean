module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.YonedaHomNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransCommonIso
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded Opposite
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

/-- 鎖同型を同じ閉次数零成分の同型として読む。 -/
def dgBarCompactComplex_closedIso {X Y : _root_.SerrePositivity.DifferentialGraded.Complex R} (e : X ≅ Y) :
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) X ≅ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) Y where
  hom := (_root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv R _ _).symm e.hom
  inv := (_root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv R _ _).symm e.inv
  hom_inv_id := by
    apply (_root_.SerrePositivity.DifferentialGraded.closedToComplex R).map_injective
    change _root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv R _ _ (_ ≫ _) = _root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv R _ _ (𝟙 _)
    rw [_root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv_comp, _root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv_id]
    change _root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv R X Y ((_root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv R X Y).symm e.hom) ≫
      _root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv R Y X ((_root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv R Y X).symm e.inv) = 𝟙 X
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact e.hom_inv_id
  inv_hom_id := by
    apply (_root_.SerrePositivity.DifferentialGraded.closedToComplex R).map_injective
    change _root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv R _ _ (_ ≫ _) = _root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv R _ _ (𝟙 _)
    rw [_root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv_comp, _root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv_id]
    change _root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv R Y X ((_root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv R Y X).symm e.inv) ≫
      _root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv R X Y ((_root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv R X Y).symm e.hom) = 𝟙 Y
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact e.inv_hom_id

/-- 元の dg Yoneda 鎖同型を、同じ成分の閉次数零同型として読む。 -/
def dgBarCompactYoneda_closedIso (x : D) (M : _root_.SerrePositivity.DifferentialGraded.RightModule R D) :
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) ((_root_.SerrePositivity.DifferentialGraded.leftRepresentable R (_root_.SerrePositivity.DifferentialGraded.representable R x)).obj M) ≅
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluationDG R D x).obj M) :=
  dgBarCompactComplex_closedIso R (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R x M)

/-- 独立の対象宇宙を許す、全 Hom と評価の共通宇宙 nerve 関手同型。 -/
def dgBarCompactYoneda_nerveIso (x : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
        (_root_.SerrePositivity.DifferentialGraded.leftRepresentable R (_root_.SerrePositivity.DifferentialGraded.representable R x)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max (u + 1) v, u + 1, w}
        (_root_.SerrePositivity.DifferentialGraded.moduleEvaluationDG R D x)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransCommonFunctorIso (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactYoneda_strict R D x)
    (dgBarCompactYoneda_closedIso R D x)
  intro M
  change _root_.SerrePositivity.DifferentialGraded.cycleFromUnit (_root_.SerrePositivity.DifferentialGraded.homComplex R (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (_root_.SerrePositivity.DifferentialGraded.representable R x) M)
      (M.obj (op x))) (_root_.SerrePositivity.DifferentialGraded.closedMap R (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R x M).hom) =
    _root_.SerrePositivity.DifferentialGraded.cycleFromUnit (_root_.SerrePositivity.DifferentialGraded.homComplex R (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (_root_.SerrePositivity.DifferentialGraded.representable R x) M)
      (M.obj (op x))) ((_root_.SerrePositivity.DifferentialGraded.complexClosedHomEquiv R _ _).symm (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso R x M).hom)
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
