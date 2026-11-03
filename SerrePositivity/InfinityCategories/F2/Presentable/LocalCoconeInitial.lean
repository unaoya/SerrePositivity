module

public import SerrePositivity.InfinityCategories.F2.Presentable.LocalTargetCocones
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulBoundary
public import SerrePositivity.InfinityCategories.Core.IdentityCocone

/-!
概要：局所終点への制限は、元の余錐圏の始対象を保持する。
方針：周囲の境界充填を局所全部分圏へ持ち上げ、引き戻しへ戻す。
規約：指定した余錐の元の頂点と射を保持。使われ方：局所置換の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {X : SSet.{u}} [Quasicategory X]

/-- 局所頂点を持つ元の余錐を、局所終点の余錐圏の指定した頂点として保持。 -/
def localTargetCoconeVertex (W : Set (X _⦋1⦌)) {K : SSet.{u}} {D : K ⟶ X}
    (c : JoinCocone D) (hc : IsLocalObject W c.vertex) : (localTargetCoconeSpace W D) _⦋0⦌ :=
  pullbackSimplex (sliceUnderProjection D) (localObjectsSubcomplex W).ι c
    ⟨c.vertex, by
      intro v
      have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
      simpa only [hv, op_id, CategoryTheory.Functor.map_id_apply] using hc⟩ rfl

/-- 局所余錐の頂点を忘れると、元の余錐そのもの。 -/
lemma localTargetCoconeVertex_fst (W : Set (X _⦋1⦌)) {K : SSet.{u}} {D : K ⟶ X}
    (c : JoinCocone D) (hc : IsLocalObject W c.vertex) :
    (pullback.fst (sliceUnderProjection D) (localObjectsSubcomplex W).ι).app
      (Opposite.op ⦋0⦌) (localTargetCoconeVertex W c hc) = c :=
  pullbackSimplex_fst _ _ _ _ _

/-- 元の余錐への像が同じ局所余錐の頂点は一致する。 -/
lemma localTargetCoconeVertex_eq_of_fst (W : Set (X _⦋1⦌))
    {K : SSet.{u}} {D : K ⟶ X} (c : (localTargetCoconeSpace W D) _⦋0⦌)
    (d : JoinCocone D) (hd : IsLocalObject W d.vertex)
    (h : (pullback.fst (sliceUnderProjection D) (localObjectsSubcomplex W).ι).app
      (Opposite.op ⦋0⦌) c = d) : c = localTargetCoconeVertex W d hd := by
  dsimp only [localTargetCoconeSpace] at c ⊢
  apply SSet.yonedaEquiv.symm.injective
  apply (cancel_mono (pullback.fst (sliceUnderProjection D) (localObjectsSubcomplex W).ι)).1
  rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp,
    localTargetCoconeVertex_fst, h]

/-- 元の余錐圏で始対象である局所余錐は、局所終点の余錐圏でも始対象。 -/
lemma localTargetCocone_isInitial_of_ambient (W : Set (X _⦋1⦌))
    {K : SSet.{u}} (D : K ⟶ X) (c : (localTargetCoconeSpace W D) _⦋0⦌)
    (hc : IsInitialVertex ((pullback.fst (sliceUnderProjection D)
      (localObjectsSubcomplex W).ι).app (Opposite.op ⦋0⦌) c)) : IsInitialVertex c := by
  intro n b hb
  let r := pullback.fst (sliceUnderProjection D) (localObjectsSubcomplex W).ι
  let q := localTargetCoconeProjection W D
  have he : boundaryVertex n 0 ≫ (b ≫ r) = SSet.yonedaEquiv.symm
      (r.app (Opposite.op ⦋0⦌) c) := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
    rfl
  obtain ⟨F, hF⟩ := hc n (b ≫ r) he
  have hι : IsFullyFaithful (localObjectsSubcomplex W).ι :=
    isFullyFaithful_fullSubcomplexOnVertices_ι X (IsLocalObject W)
  have : InnerFibration (localObjectsSubcomplex W).ι :=
    inferInstanceAs (InnerFibration (fullSubcomplexOnVertices X (IsLocalObject W)).ι)
  have := hι.hasLiftingProperty_boundary_succ n
  have hw : (b ≫ q) ≫ (localObjectsSubcomplex W).ι =
      (boundary (n + 1)).ι ≫ (F ≫ sliceUnderProjection D) := by
    rw [← Category.assoc, hF, Category.assoc]
    exact congrArg (fun f ↦ b ≫ f) (pullback.condition (f := sliceUnderProjection D)
      (g := (localObjectsSubcomplex W).ι)).symm
  let sq : CommSq (b ≫ q) (boundary (n + 1)).ι (localObjectsSubcomplex W).ι
      (F ≫ sliceUnderProjection D) := ⟨hw⟩
  refine ⟨pullback.lift F sq.lift sq.fac_right.symm, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    exact hF
  · rw [Category.assoc, pullback.lift_snd]
    exact sq.fac_left

end SerrePositivity.InfinityCategories.HomotopyLimits
