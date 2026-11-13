module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedPrecompositionIdentity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedChainMapComposition

/-! # 閉零圏上の実 pinched Hom 反変関手

概要：始点を閉零圏で動かし、実 pinched 写像空間と閉射による前合成を関手にする。
方針：前合成鎖写像の恒等・合成則を実 pinched 鎖写像へ移す。
規約：元の対象宇宙と Hom 宇宙を独立に保つ。使われ方：実分母の屋根図式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Opposite DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 閉零圏の始点に関する、実 pinched Hom の反変関手。 -/
def dgClosedPinchedRepresentable (y : D) : (_root_.SerrePositivity.DifferentialGraded.ClosedCategory A D)ᵒᵖ ⥤ SSet.{max u v} where
  obj q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) q.unop) y
  map {q p} r := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D
    (q := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) p.unop)
    (x := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) q.unop) (y := y) r.unop)
  map_id q := (congrArg _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_id A D
    (x := ForgetEnrichment.to (Complex A) q.unop) (y := y))).trans _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_id
  map_comp r s := by
    change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D (y := y) (s.unop ≫ r.unop)) = _
    rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap_comp]

/-- 反変関手の指定閉射上の値は、元の実 pinched 前合成そのもの。 -/
lemma dgClosedPinchedRepresentable_map (y : D) {p q : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D} (r : p ⟶ q) :
    (dgClosedPinchedRepresentable A D y).map r.op =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D
        (q := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) p) (x := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) q)
        (y := y) r) := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
