module
public import SerrePositivity.KST.Spectra.FibrationExactness
public import SerrePositivity.KST.Spectra.HomotopyIso

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
open scoped Simplicial
namespace SerrePositivity.KST.LocalizingInvariants.CoreFlag
open Spectra

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
    KanFiber q (q.app _ a) ≅ KanFiber p (p.app _ (s.app _ a)) := by
  have hb := pullback_basepoint h a
  let f : KanFiber q (q.app _ a) ⟶ KanFiber p (p.app _ (s.app _ a)) :=
    fiberLift p _ (fiberι q _ ≫ s) (by
      rw [Category.assoc, ← h.w, ← Category.assoc, fiberι_comp, const_comp, hb])
  let t : KanFiber p (p.app _ (s.app _ a)) ⟶ P :=
    h.lift (SSet.const (q.app _ a)) (fiberι p _) (by rw [const_comp, hb, fiberι_comp])
  let k : KanFiber p (p.app _ (s.app _ a)) ⟶ KanFiber q (q.app _ a) :=
    fiberLift q _ t (h.lift_fst _ _ _)
  refine ⟨f, k, ?_, ?_⟩
  · apply fiber_hom_ext q (q.app _ a)
    change f ≫ k ≫ fiberι q _ = 𝟙 _ ≫ fiberι q _
    dsimp only [k]
    rw [fiberLift_ι, Category.id_comp]
    apply h.hom_ext
    · dsimp only [t]
      rw [Category.assoc, h.lift_fst, comp_const, fiberι_comp]
    · dsimp only [t, f]
      rw [Category.assoc, h.lift_snd, fiberLift_ι]
  · apply fiber_hom_ext p (p.app _ (s.app _ a))
    change k ≫ f ≫ fiberι p _ = 𝟙 _ ≫ fiberι p _
    dsimp only [f, k]
    rw [fiberLift_ι, ← Category.assoc, fiberLift_ι]
    dsimp only [t]
    rw [h.lift_snd, Category.id_comp]

@[reassoc (attr := simp)]
lemma pullbackFiberIso_hom_ι (h : IsPullback q s g p) (a : P _⦋0⦌) :
    (pullbackFiberIso h a).hom ≫ fiberι p _ = fiberι q _ ≫ s := by
  simp only [pullbackFiberIso, fiberLift_ι]

/-- 元の fiber の包含の零次成分は単射。 -/
lemma fiber_vertex_ext {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    {v w : (KanFiber p b) _⦋0⦌} (hv : (fiberι p b).app _ v = (fiberι p b).app _ w) :
    v = w := by
  apply SSet.yonedaEquiv.symm.injective
  apply fiber_hom_ext p b
  apply SSet.yonedaEquiv.injective
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using hv

@[simp]
lemma pullbackFiberIso_point (h : IsPullback q s g p) (a : P _⦋0⦌) :
    (pullbackFiberIso h a).hom.app _ (fiberPoint q a) = fiberPoint p (s.app _ a) := by
  apply fiber_vertex_ext p _
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, pullbackFiberIso_hom_ι]
  change s.app _ ((fiberι q _).app _ (fiberPoint q a)) = _
  rw [fiberι_point, fiberι_point]

end SerrePositivity.KST.LocalizingInvariants.CoreFlag
