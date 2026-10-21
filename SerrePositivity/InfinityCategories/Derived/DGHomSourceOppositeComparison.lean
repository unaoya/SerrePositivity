module
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetSpaceComparison
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet Opposite HomologicalComplex
open CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
/-- dg 反対圏の左 representable は、元の右 representable と全次数で等しい。 -/
lemma dgLeftRepresentableOpposite_eq (x : C) :
    leftRepresentable R (op x) = (representable R x).toFunctor := by
  apply EnrichedFunctor.ext (Complex R)
    (F := leftRepresentable R (op x)) (G := (representable R x).toFunctor) (fun _ => rfl)
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
  change leftAction R (leftRepresentable R (op x)) f h hn =
    ((representableMap R x y z).f p f).v q n hn h
  rw [leftRepresentable_action, representableMap_apply,
    opposite_forward R C (op x) y z q p n hn]
  rw [Int.mul_comm q p, ← mul_smul]
  simp
/-- 同じ等式は、R 加群値の実 Hom dg 関手全体の等式を与える。 -/
lemma dgHomTargetModuleDG_opposite (x : C) :
    dgHomTargetModuleDG R Cᵒᵖ (op x) =
      (representable R x).toFunctor.comp (ringConstantDG R) := by
  rw [dgHomTargetModuleDG, dgLeftRepresentableOpposite_eq]
end SerrePositivity.InfinityCategories
