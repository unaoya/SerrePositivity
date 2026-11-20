module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationExactness
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso

/-!
概要：厳密な Kan 引き戻しの二つの基点付き fiber の同型。
方針：指定された引き戻しの普遍性で逆写像を作る。
規約：元の射影と元の基点を保持する。
使われ方：Sp-8 (3)、KanPullbackCofinalityInput の完全列比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CoreFlag
end SerrePositivity.KST.LocalizingInvariants.CoreFlag
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.CoreFlag
open _root_.SerrePositivity.KST.Spectra

variable {P X E B : SSet.{u}} {q : P ⟶ X} {s : P ⟶ E} {g : X ⟶ B} {p : E ⟶ B}

/-- 任意の指定された厳密引き戻しの第一射影も Kan fibration。 -/
lemma pullback_fibration (h : IsPullback q s g p) (hp : J.rlp p) : Fibration q := by
  apply (SSet.modelCategoryQuillen.fibration_iff q).mpr
  exact J.rlp.of_isPullback h.flip hp

/-- 厳密引き戻しの基点の像は可換。 -/
lemma pullback_basepoint (h : IsPullback q s g p) (a : P _⦋0⦌) :
    g.app _ (q.app _ a) = p.app _ (s.app _ a) :=
  ConcreteCategory.congr_hom (congr_app h.w _) a

/-- 厳密引き戻しの二つの fiber は、元の基点において同型。 -/
def pullbackFiberIso (h : IsPullback q s g p) (a : P _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber q (q.app _ a) ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ (s.app _ a)) := by
  have hb := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.pullback_basepoint h a
  let f : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber q (q.app _ a) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ (s.app _ a)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift p _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι q _ ≫ s) (by
      rw [Category.assoc, ← h.w, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp, const_comp, hb])
  let t : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ (s.app _ a)) ⟶ P :=
    h.lift (SSet.const (q.app _ a)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p _) (by rw [const_comp, hb, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp])
  let k : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ (s.app _ a)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber q (q.app _ a) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift q _ t (h.lift_fst _ _ _)
  refine ⟨f, k, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext q (q.app _ a)
    change f ≫ k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι q _ = 𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι q _
    dsimp only [k]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι, Category.id_comp]
    apply h.hom_ext
    · dsimp only [t]
      rw [Category.assoc, h.lift_fst, comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp]
    · dsimp only [t, f]
      rw [Category.assoc, h.lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι]
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p (p.app _ (s.app _ a))
    change k ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p _ = 𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p _
    dsimp only [f, k]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι]
    dsimp only [t]
    rw [h.lift_snd, Category.id_comp]

@[reassoc (attr := simp)]
lemma pullbackFiberIso_hom_ι (h : IsPullback q s g p) (a : P _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.pullbackFiberIso h a).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p _ = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι q _ ≫ s := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.pullbackFiberIso, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι]

/-- 元の fiber の包含の零次成分は単射。 -/
lemma fiber_vertex_ext {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    {v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b) _⦋0⦌} (hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b).app _ v = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b).app _ w) :
    v = w := by
  apply SSet.yonedaEquiv.symm.injective
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p b
  apply SSet.yonedaEquiv.injective
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using hv

@[simp]
lemma pullbackFiberIso_point (h : IsPullback q s g p) (a : P _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.pullbackFiberIso h a).hom.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint q a) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p (s.app _ a) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.fiber_vertex_ext p _
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag.pullbackFiberIso_hom_ι]
  change s.app _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι q _).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint q a)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreFlag

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
