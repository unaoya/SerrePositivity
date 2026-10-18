module
public import SerrePositivity.InfinityCategories.F1.CoreKan
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful

/-! # trivial Kan fibration の core への制限
概要：quasicategory 間の trivial Kan fibration は core 上でも trivial Kan fibration。
方針：元の境界充填を取り、充満忠実性による辺の可逆性の反映で core に持ち上げる。
規約：F1 の core の定義や公開 API は変更しない。使われ方：S₁ の比較の Kan 模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：trivial Kan fibration を core に制限しても全境界を充填できる。
方針：元の充填の辺は像が可逆で、充満忠実性により元も可逆となる。
規約：両端は quasicategory。使われ方：S₁ と元の圏の core の比較。 -/
lemma coreMap_trivialKanFibration {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (f : X ⟶ Y) [TrivialKanFibration f] : TrivialKanFibration (quasicategoryCoreMap f) := by
  have hf := (isQCatEquivalence_of_trivialKanFibration f).isFullyFaithful
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  have : HasLiftingProperty (boundary n).ι f :=
    (trivialKanFibration_iff_boundary f).1 inferInstance n
  constructor
  intro a b sq
  let sq' : CommSq (a ≫ (quasicategoryCore X).ι) (boundary n).ι f
      (b ≫ (quasicategoryCore Y).ι) := ⟨by
    rw [Category.assoc, ← quasicategoryCoreMap_ι, ← Category.assoc, sq.w, Category.assoc]⟩
  let l := sq'.lift
  let q : (Δ[n] : SSet.{u}) ⟶ (quasicategoryCore X : SSet.{u}) :=
    quasicategoryCoreLift l (fun s => by
      apply hf.reflects_isInvertibleEdge (edgeOfSimplex (l.app (Opposite.op ⦋1⦌) s))
      apply (isInvertibleEdge_congr
        (e := (edgeOfSimplex (l.app (Opposite.op ⦋1⦌) s)).map ((truncation 2).map f))
        (f := edgeOfSimplex (f.app (Opposite.op ⦋1⦌)
          (l.app (Opposite.op ⦋1⦌) s))) rfl).mpr
      have he := ConcreteCategory.congr_hom
        (NatTrans.congr_app sq'.fac_right (Opposite.op ⦋1⦌)) s
      change f.app (Opposite.op ⦋1⦌) (l.app (Opposite.op ⦋1⦌) s) =
        (b.app (Opposite.op ⦋1⦌) s).val at he
      rw [he]
      exact quasicategoryCore_edge (b.app (Opposite.op ⦋1⦌) s))
  refine CommSq.HasLift.mk' { l := q, fac_left := ?_, fac_right := ?_ }
  · apply (cancel_mono (quasicategoryCore X).ι).1
    change (boundary n).ι ≫ l = a ≫ (quasicategoryCore X).ι
    exact sq'.fac_left
  · apply (cancel_mono (quasicategoryCore Y).ι).1
    rw [Category.assoc, quasicategoryCoreMap_ι, ← Category.assoc]
    change l ≫ f = b ≫ (quasicategoryCore Y).ι
    exact sq'.fac_right

end SerrePositivity.KST.SConstruction
