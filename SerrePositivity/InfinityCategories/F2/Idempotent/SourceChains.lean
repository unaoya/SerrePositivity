module

public import SerrePositivity.InfinityCategories.F2.Idempotent.IdentityCollapseChain

/-!
概要：全頂点が元の非分裂対象である全 nerve 単体を、元の Idem 単体へ戻す。
方針：元の全射の値を取り、対象の等式による恒等輸送まで照合する。
規約：全単体を元の包含で厳密に回収する。対象列だけの一致で代用しない。
使われ方：元の Idem 包含を元の全部分複体の包含と同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 全頂点が元の非分裂対象である単体から、元の全 Idem 単体を構成する。 -/
def sourceChain {n : ℕ} (F : ComposableArrows WalkingSplit.{u} n)
    (hF : ∀ i, F.obj i = walkingSource) : ComposableArrows WalkingIdem.{u} n where
  obj _ := walkingObject
  map f := (F.map f).f
  map_id i := by
    have h := congrArg CategoryTheory.Idempotents.Karoubi.Hom.f (F.map_id i)
    exact h.trans (congrArg (fun P : WalkingSplit.{u} ↦ walkingScalar P.p) (hF i))
  map_comp f g := congrArg CategoryTheory.Idempotents.Karoubi.Hom.f (F.map_comp f g)

/-- 元の構成した全 Idem 単体の包含像は、元の全単体そのもの。 -/
lemma sourceChain_inclusion {n : ℕ} (F : ComposableArrows WalkingSplit.{u} n)
    (hF : ∀ i, F.obj i = walkingSource) : sourceChain F hF ⋙ walkingInclusion = F := by
  refine CategoryTheory.Functor.ext (fun i ↦ (hF i).symm) ?_
  intro i j f
  apply CategoryTheory.Idempotents.Karoubi.Hom.ext
  have hi := walkingScalar_eqToHom_source (hF i).symm rfl
  have hj := walkingScalar_eqToHom_source (hF j) (hF j)
  change walkingScalar (F.map f).f =
    (walkingScalar (eqToHom (hF j)).f * walkingScalar (F.map f).f) *
      walkingScalar (eqToHom (hF i).symm).f
  rw [hi, hj, one_mul, mul_one]

end SerrePositivity.InfinityCategories.F2.Idempotent
