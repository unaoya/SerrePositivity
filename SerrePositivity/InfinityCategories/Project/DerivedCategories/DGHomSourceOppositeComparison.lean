module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGHomTargetSpaceComparison
/-!
概要：dg 反対圏の共変 Hom と元の反変 Hom を全次数で同定する。
方針：左作用と反対合成の二つの Koszul 符号を打ち消す。
規約：元の全 Hom 鎖写像を比較する。使われ方：反変 Hom の全関手比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet Opposite HomologicalComplex
open CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- dg 反対圏の左 representable は、元の右 representable と全次数で等しい。 -/
lemma dgLeftRepresentableOpposite_eq (x : C) :
    _root_.SerrePositivity.DifferentialGraded.leftRepresentable R (_root_.Opposite.op x) = (_root_.SerrePositivity.DifferentialGraded.representable R x).toFunctor := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R)
    (F := _root_.SerrePositivity.DifferentialGraded.leftRepresentable R (_root_.Opposite.op x)) (G := (_root_.SerrePositivity.DifferentialGraded.representable R x).toFunctor) (fun _ => rfl)
  intro y z
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Cochain.ext
  intro q n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  change _root_.SerrePositivity.DifferentialGraded.leftAction R (_root_.SerrePositivity.DifferentialGraded.leftRepresentable R (_root_.Opposite.op x)) f h hn =
    ((_root_.SerrePositivity.DifferentialGraded.representableMap R x y z).f p f).v q n hn h
  rw [_root_.SerrePositivity.DifferentialGraded.leftRepresentable_action, _root_.SerrePositivity.DifferentialGraded.representableMap_apply,
    _root_.SerrePositivity.DifferentialGraded.opposite_forward R C (_root_.Opposite.op x) y z q p n hn]
  rw [Int.mul_comm q p, ← mul_smul]
  simp
/-- 同じ等式は、R 加群値の実 Hom dg 関手全体の等式を与える。 -/
lemma dgHomTargetModuleDG_opposite (x : C) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG R Cᵒᵖ (_root_.Opposite.op x) =
      (_root_.SerrePositivity.DifferentialGraded.representable R x).toFunctor.comp (_root_.SerrePositivity.DifferentialGraded.ringConstantDG R) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleDG, dgLeftRepresentableOpposite_eq]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
