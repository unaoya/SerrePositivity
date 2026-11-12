module
public import SerrePositivity.KST.Comparison.SliceAdjunction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal

/-! # 単体で全射な基底変換による境界持ち上げ性の検出
概要：全単体で全射な基底変換の後に自明 Kan fibration となる射は、元から自明 Kan fibration。
方針：下辺の標準単体を被覆側へ持ち上げ、その境界を厳密な引き戻しへ移して充填する。
規約：基底の Kan 性は不要。使われ方：連結な基底上の homotopy pullback の検出。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Comparison
open scoped Simplicial

/-- 全単体で全射な基底変換は自明 Kan fibration を反映する。 -/
lemma trivialKanFibration_of_simplexSurjective_baseChange {E B : SSet.{u}} (t : E ⟶ B)
    (ht : ∀ n : ℕ, Function.Surjective (t.app (Opposite.op ⦋n⦌)))
    {X Y : Over B} (f : X ⟶ Y)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((sliceFiberFunctor t).map f)] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration f.left := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).mpr
  intro n
  constructor
  intro a b sq
  obtain ⟨e, he⟩ := ht n (SSet.yonedaEquiv (b ≫ Y.hom))
  let v : (Δ[n] : SSet.{u}) ⟶ E := SSet.yonedaEquiv.symm e
  have hv : v ≫ t = b ≫ Y.hom := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    exact (congrArg (t.app (Opposite.op ⦋n⦌)) (SSet.yonedaEquiv.apply_symm_apply e)).trans he
  let a' : (boundary n : SSet.{u}) ⟶ pullback X.hom t :=
    pullback.lift a ((boundary n).ι ≫ v) (by
      rw [Category.assoc, hv, ← Category.assoc, ← sq.w, Category.assoc, Over.w f])
  let b' : (Δ[n] : SSet.{u}) ⟶ pullback Y.hom t := pullback.lift b v hv.symm
  let q : pullback X.hom t ⟶ pullback Y.hom t := (sliceFiberFunctor t).map f
  have hqf : q ≫ pullback.fst Y.hom t = pullback.fst X.hom t ≫ f.left :=
    sliceFiberFunctor_map_fst t f
  have hqs : q ≫ pullback.snd Y.hom t = pullback.snd X.hom t :=
    sliceFiberFunctor_map_snd t f
  let : HasLiftingProperty (boundary n).ι q :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary q).mp inferInstance n
  have sq' : CommSq a' (boundary n).ι q b' := by
    constructor
    apply pullback.hom_ext
    · rw [Category.assoc, hqf, ← Category.assoc,
        pullback.lift_fst, Category.assoc, pullback.lift_fst]
      exact sq.w
    · rw [Category.assoc, hqs, pullback.lift_snd,
        Category.assoc, pullback.lift_snd]
  let l := sq'.lift
  have hl := sq'.fac_left
  have hr := sq'.fac_right
  refine CommSq.HasLift.mk' {
    l := l ≫ pullback.fst X.hom t
    fac_left := ?_
    fac_right := ?_ }
  · rw [← Category.assoc, hl, pullback.lift_fst]
  · rw [Category.assoc, ← hqf, ← Category.assoc, hr,
      pullback.lift_fst]

end SerrePositivity.KST.SConstruction
