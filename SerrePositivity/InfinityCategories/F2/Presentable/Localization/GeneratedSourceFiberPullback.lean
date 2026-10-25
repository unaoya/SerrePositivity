module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.SourceArrowFiber
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullRestrictionPullback

/-!
概要：閉包内射の固定始域比較を、周囲の全 coslice と射圏 fiber の比較の引き戻しにする。
方針：元の脚の全単体と頂点条件を保持し、全部分圏の持ち上げの普遍性を検査する。
規約：この引き戻しだけから accessibility や presentable 性は主張しない。
使われ方：固定始域圏の実比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 閉包内射の厳密な始点 fiber を、周囲の同じ始点 fiber へ含める。 -/
def generatedSourceArrowFiberInclusion (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    generatedSourceArrowFiber edges x ⟶ vertexFiber
      (evaluateFunctorAt (Y := C) (stdSimplex.obj₀Equiv.symm 0 : Δ[1] _⦋0⦌)) x :=
  vertexFiberLift _ x (vertexFiberι
    (generatedArrowInclusion edges ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)) x ≫
      generatedArrowInclusion edges) (by rw [Category.assoc, vertexFiberι_comp])

/-- 厳密な fiber の包含は、元の同じ全射族を保持する。 -/
lemma generatedSourceArrowFiberInclusion_ι (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    generatedSourceArrowFiberInclusion edges x ≫ vertexFiberι
      (evaluateFunctorAt (Y := C) (stdSimplex.obj₀Equiv.symm 0 : Δ[1] _⦋0⦌)) x =
      vertexFiberι (generatedArrowInclusion edges ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)) x ≫ generatedArrowInclusion edges :=
  vertexFiberLift_ι _ _ _ _

instance generatedSourceArrowFiberInclusion_mono (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    Mono (generatedSourceArrowFiberInclusion edges x) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : (vertexFiber
    (evaluateFunctorAt (Y := C) (stdSimplex.obj₀Equiv.symm 0 : Δ[1] _⦋0⦌)) x).obj n ↦ z.val) hab

/-- 元の固定始域比較は、周囲の全 coslice の比較と厳密に可換。 -/
lemma generatedSourceFiber_square (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    generatedSourceInclusion edges x ≫ (sourceCosliceArrowFiberEquivalence x).hom =
      generatedSourceToArrowFiber edges x ≫ generatedSourceArrowFiberInclusion edges x := by
  apply vertexFiber_hom_ext _ x
  rw [Category.assoc, sourceCosliceArrowFiberEquivalence_inclusion,
    Category.assoc, generatedSourceArrowFiberInclusion_ι, ← Category.assoc,
    generatedSourceToArrowFiber_inclusion, generatedSourceArrows_inclusion]

/-- 閉包内射の固定始域比較は、周囲の全比較の実際の引き戻し。 -/
lemma generatedSourceFiber_isPullback (edges : I → C _⦋1⦌) (x : C _⦋0⦌) :
    IsPullback (generatedSourceInclusion edges x) (generatedSourceToArrowFiber edges x)
      (sourceCosliceArrowFiberEquivalence x).hom (generatedSourceArrowFiberInclusion edges x) := by
  have : Mono (generatedSourceInclusion edges x) := by
    change Mono (fullSubcomplexOnVertices (sliceUnder (SSet.yonedaEquiv.symm x))
      (fun c ↦ (JoinCocone.leg c (𝟙 Δ[0])).edge ∈ generatedEdges edges)).ι
    infer_instance
  refine IsPullback.mk' (generatedSourceFiber_square edges x) ?_ ?_
  · intro T a b ha hb
    exact (cancel_mono (generatedSourceInclusion edges x)).mp ha
  · intro T a b hab
    let L := fullSubcomplexLift
      (fun c : JoinCocone (SSet.yonedaEquiv.symm x) ↦
        (JoinCocone.leg c (𝟙 Δ[0])).edge ∈ generatedEdges edges) a (by
      intro t
      have he := congrArg (fun f ↦ f ≫ vertexFiberι
        (evaluateFunctorAt (Y := C) (stdSimplex.obj₀Equiv.symm 0 : Δ[1] _⦋0⦌)) x) hab
      rw [Category.assoc, sourceCosliceArrowFiberEquivalence_inclusion,
        Category.assoc, generatedSourceArrowFiberInclusion_ι] at he
      have ht := ConcreteCategory.congr_hom (NatTrans.congr_app he (Opposite.op ⦋0⦌)) t
      have hm := fullSubcomplexOnVertices_vertex (b.app _ t).val
      rw [← sourceCosliceArrowFamily_vertex x (a.app _ t)]
      exact congrArg arrowVertexEdge ht ▸ hm)
    have hL : L ≫ generatedSourceInclusion edges x = a := fullSubcomplexLift_ι _ _ _
    refine ⟨L, hL, ?_⟩
    apply (cancel_mono (generatedSourceArrowFiberInclusion edges x)).mp
    rw [Category.assoc, ← generatedSourceFiber_square, ← Category.assoc,
      hL]
    exact hab

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
