module

public import SerrePositivity.InfinityCategories.F2.Idempotent.FullSlicePullback
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionTerminal
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionRestrictionImage

/-!
概要：元の任意の冪等完備化は、元の図式に既に存在する全極限錐を保存する。
方針：全部分圏の slice の引き戻しで終対象保存を適用し、頂点像への同値で一般化。
規約：添字の有限性・quasicategory 性や元の射の inner 性を仮定しない。
使われ方：HA 1.1.3.7 の既存の有限極限と fiber 四角形の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 全部分圏としての元の冪等完備化は、同じ元の全極限錐を保存する。 -/
lemma mapJoinCone_isLimit_fullCompletion {K X : SSet.{u}} [Quasicategory X]
    (P : X _⦋0⦌ → Prop)
    (hP : IsIdempotentCompletion (fullSubcomplexOnVertices X P).ι)
    {p : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u})}
    (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone (fullSubcomplexOnVertices X P).ι c) := by
  let i := (fullSubcomplexOnVertices X P).ι
  let q := sliceOverProjection (p ≫ i)
  have : InnerFibration (pullback.snd i q) :=
    ⟨innerFibrations.pullback_snd i q (InnerFibration.mem (q := i))⟩
  have : Quasicategory (pullback i q) := quasicategory_of_innerFibration (pullback.snd i q)
  let e := (fullSliceOver_isPullback P p).isoPullback
  have ht : IsTerminalVertex (e.hom.app (Opposite.op ⦋0⦌) c) :=
    hc.map_of_isIso e.hom
  have h := IsIdempotentCompletion.map_isTerminalVertex (pullback.snd i q)
    (IsIdempotentCompletion.sliceOver i hP (p ≫ i)) ht
  change IsTerminalVertex ((e.hom ≫ pullback.snd i q).app (Opposite.op ⦋0⦌) c) at h
  rw [show e.hom ≫ pullback.snd i q = sliceOverPostcomp p i from
    (fullSliceOver_isPullback P p).isoPullback_hom_snd] at h
  exact h

/-- 元の任意の冪等完備化は、元の全図式の指定極限錐の同じ像を極限錐へ送る。 -/
lemma IsIdempotentCompletion.mapJoinCone_isLimit {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : IsIdempotentCompletion f)
    {p : K ⟶ C} (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone f c) := by
  let P := fun y ↦ ∃ x, f.app (Opposite.op ⦋0⦌) x = y
  let e := fullSubcomplexLift P f (fun x ↦ ⟨x, rfl⟩)
  let i := (fullSubcomplexOnVertices D P).ι
  have hi : IsIdempotentCompletion i := IsIdempotentCompletion.vertexImage f hf
  have he : IsQCatEquivalence e := fullSubcomplexVertexImageLift_isQCatEquivalence f hf.2.1
  have hfac : e ≫ i = f := fullSubcomplexLift_ι _ _ _
  have h := mapJoinCone_isLimit_fullCompletion P hi (mapJoinCone e c)
    ((he.isLimitCone_iff c).mp hc)
  exact (isLimitCone_iff_of_diagram_eq
    (by rw [Category.assoc, hfac])
    (show (c.val ≫ e) ≫ i = c.val ≫ f by rw [Category.assoc, hfac])).mp h

/-- 元の任意の冪等完備化は、元の図式の極限の存在をその同じ像へ移す。 -/
lemma IsIdempotentCompletion.hasLimit_comp {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (f : C ⟶ D) (hf : IsIdempotentCompletion f)
    (p : K ⟶ C) (hp : HasLimit p) : HasLimit (p ≫ f) := by
  obtain ⟨c, hc⟩ := hp
  exact ⟨mapJoinCone f c, IsIdempotentCompletion.mapJoinCone_isLimit f hf c hc⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
