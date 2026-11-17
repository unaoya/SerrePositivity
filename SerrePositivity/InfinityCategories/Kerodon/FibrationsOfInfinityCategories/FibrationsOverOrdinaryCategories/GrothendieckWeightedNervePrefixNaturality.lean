module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.GrothendieckWeightedNervePrefix

/-!
概要：同じGrothendieck射列のprefixは、初区間の包含と元の基底の射に自然。
方針：元のCostructuredArrowの脚の合成を照合し、既存transport_naturalityを使う。
規約：IS-W2 R03eの前向きの単体の自然性・合成則。脚や対象を選び直さない。
使われ方：全prefixを同じsimplexPrefixWeightからの自然変換へ束ねる。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {I : Type u} [SmallCategory I] (F : I ⥤ Cat.{u,u})
  {n : ℕ} (σ : ComposableArrows (Grothendieck F) n)

/-- 元のprefixの脚は、同じ最終基底の射での後合成と厳密に両立する。 -/
theorem grothWeightedPrefixArrow_naturality {i j : Fin (n+1)} (f : i ⟶ j) :
    grothWeightedPrefixArrow F σ i ⋙ CostructuredArrow.map (S := Grothendieck.forget F) (σ.map f).base =
      (simplexPrefixInclusion i.val j.val (leOfHom f)).toOrderHom.monotone.functor ⋙
        grothWeightedPrefixArrow F σ j := by
  refine CategoryTheory.Functor.ext (fun k => ?_) ?_
  · change CostructuredArrow.mk (S := Grothendieck.forget F) (Y := σ.obj (grothWeightedPrefixIndex i k)) ((σ.map (homOfLE
      (show grothWeightedPrefixIndex i k ≤ i from Nat.le_of_lt_succ k.isLt))).base ≫
        (σ.map f).base) = CostructuredArrow.mk (S := Grothendieck.forget F) (Y := σ.obj (grothWeightedPrefixIndex i k)) ((σ.map (homOfLE
          (show grothWeightedPrefixIndex i k ≤ j from (Nat.le_of_lt_succ k.isLt).trans (leOfHom f)))).base)
    apply congrArg (fun a : (σ.obj (grothWeightedPrefixIndex i k)).base ⟶ (σ.obj j).base =>
      CostructuredArrow.mk (S := Grothendieck.forget F) (Y := σ.obj (grothWeightedPrefixIndex i k)) a)
    have hc := (congrArg (fun a => a.base) (σ.map_comp
      (homOfLE (show grothWeightedPrefixIndex i k ≤ i from Nat.le_of_lt_succ k.isLt)) f)).symm
    have he : homOfLE (show grothWeightedPrefixIndex i k ≤ i from Nat.le_of_lt_succ k.isLt) ≫ f =
      homOfLE (show grothWeightedPrefixIndex i k ≤ j from (Nat.le_of_lt_succ k.isLt).trans (leOfHom f)) :=
      Subsingleton.elim _ _
    simpa only [Grothendieck.comp_base, he] using hc
  · intro k l g
    apply CostructuredArrow.hom_ext
    simp only [CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
    change σ.map (homOfLE (show grothWeightedPrefixIndex i k ≤ grothWeightedPrefixIndex i l from leOfHom g)) =
      eqToHom rfl ≫ σ.map (homOfLE (show grothWeightedPrefixIndex i k ≤ grothWeightedPrefixIndex i l from leOfHom g)) ≫ eqToHom rfl
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 同じfiber prefixは、全初区間の包含で元の同じfiber関手へ移る。 -/
theorem grothWeightedPrefixFiber_naturality {i j : Fin (n+1)} (f : i ⟶ j) :
    (simplexPrefixInclusion i.val j.val (leOfHom f)).toOrderHom.monotone.functor ⋙
        grothWeightedPrefixFiber F σ j =
      grothWeightedPrefixFiber F σ i ⋙ (F.map (σ.map f).base).toFunctor := by
  change _ ⋙ (grothWeightedPrefixArrow F σ j ⋙ transport F (σ.obj j).base) = _
  rw [← Functor.assoc, ← grothWeightedPrefixArrow_naturality F σ f,
    Functor.assoc, transport_naturality]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
