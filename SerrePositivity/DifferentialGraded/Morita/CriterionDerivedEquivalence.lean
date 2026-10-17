module
public import SerrePositivity.DifferentialGraded.Morita.CriterionDerivedFullyFaithful
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfEquivalence

/-! # Perf上の同値から全主導来圏へのMorita拡張

Perf判定の結論は明示した入力とする。両側のcompact生成を保持し、
右随伴・その一致・unit/counitとの比較は構成しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z z'
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)

/-- 実際のPerf制限の同値から、元の関手のPerf対象間のHom比較を取り出す。 -/
lemma criterionDerivedHom_of_perfectEquivalence
    (hperf : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    [(perfectFunctorRestriction A D E T hperf).IsEquivalence]
    (X Y : DerivedModuleCategory A D) (hX : modulePerfect A D X) (hY : modulePerfect A D Y) :
    Function.Bijective (fun f : X ⟶ Y => T.map f) := by
  let F := perfectFunctorRestriction A D E T hperf
  let X' : PerfectModuleCategory A D := ⟨X, hX⟩
  let Y' : PerfectModuleCategory A D := ⟨Y, hY⟩
  constructor
  · intro f g h
    change T.map f = T.map g at h
    have he : F.map (ObjectProperty.homMk f : X' ⟶ Y') =
        F.map (ObjectProperty.homMk g : X' ⟶ Y') := (modulePerfect A E).hom_ext h
    exact congrArg (fun k : X' ⟶ Y' => k.hom) (F.map_injective he)
  · intro g
    obtain ⟨f, hf⟩ := F.map_surjective (ObjectProperty.homMk g : F.obj X' ⟶ F.obj Y')
    exact ⟨f.hom, congrArg (fun k : F.obj X' ⟶ F.obj Y' => k.hom) hf⟩

/-- 実際のPerf制限の本質的全射を、主導来圏での本質的像として読む。 -/
lemma criterionDerivedImage_of_perfectEquivalence
    (hperf : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    [(perfectFunctorRestriction A D E T hperf).EssSurj]
    (Y : DerivedModuleCategory A E) (hY : modulePerfect A E Y) : T.essImage Y := by
  let F := perfectFunctorRestriction A D E T hperf
  let Y' : PerfectModuleCategory A E := ⟨Y, hY⟩
  exact ⟨(F.objPreimage Y').obj,
    ⟨(perfectModuleInclusion A E Set.univ).mapIso (F.objObjPreimageIso Y')⟩⟩

variable [T.CommShift ℤ] [T.IsTriangulated]

/-- 明示した両側のcompact生成の下で、Perf同値を全主導来圏の同値性へ拡張する。 -/
lemma criterionDerivedIsEquivalence_of_perfectEquivalence
    (hperf : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    [(perfectFunctorRestriction A D E T hperf).IsEquivalence]
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H)
    (hcop : ∀ K : Type u, PreservesColimitsOfShape (Discrete K) T) : T.IsEquivalence := by
  let hff := criterionDerivedFullyFaithful A D E T G hG hcop hperf
    (criterionDerivedHom_of_perfectEquivalence A D E T hperf)
  let : T.Full := hff.full
  let : T.Faithful := hff.faithful
  let : T.EssSurj := criterionDerivedEssSurj_of_perfectImage A D E T hcop H hH
    (criterionDerivedImage_of_perfectEquivalence A D E T hperf)
  exact {}

/-- 順関手を元の実際の関手のままに保つ、条件付きの全主導来圏同値。 -/
def criterionDerivedEquivalence_of_perfectEquivalence
    (hperf : ∀ X, modulePerfect A D X → modulePerfect A E (T.obj X))
    [(perfectFunctorRestriction A D E T hperf).IsEquivalence]
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H)
    (hcop : ∀ K : Type u, PreservesColimitsOfShape (Discrete K) T) :
    DerivedModuleCategory A D ≌ DerivedModuleCategory A E := by
  have := criterionDerivedIsEquivalence_of_perfectEquivalence A D E T hperf G hG H hH hcop
  exact T.asEquivalence

omit [T.CommShift ℤ] [T.IsTriangulated]

/-- 一般kernelのPerf同値から、実際の主導来作用の同値性を得る。
三角性と余積保存は既存の実際の作用のAPIから供給する。 -/
lemma criterionDerivedKernelIsEquivalence (K : Kernel A D E)
    (hK : kernelColumnsPerfect A D E K)
    [(perfectDerivedKernelAction A D E K hK).IsEquivalence]
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    (kernelDerivedTensor A D E K).IsEquivalence := by
  let := criterionPerfKernelCommShift A D E K
  let := criterionPerfKernelIsTriangulated A D E K
  let hperf : ∀ X, modulePerfect A D X →
      modulePerfect A E ((kernelDerivedTensor A D E K).obj X) :=
    fun _ h => perfectDerivedKernelAction_preserves A D E K hK h
  let : (perfectFunctorRestriction A D E (kernelDerivedTensor A D E K) hperf).IsEquivalence := by
    change (perfectDerivedKernelAction A D E K hK).IsEquivalence
    infer_instance
  exact criterionDerivedIsEquivalence_of_perfectEquivalence A D E
    (kernelDerivedTensor A D E K) hperf G hG H hH
    (fun J => criterionDerivedKernelPreservesCoproducts A D E K J)

/-- compact生成を明示した、一般kernelによる全主導来圏のMorita同値。 -/
def criterionDerivedKernelEquivalence (K : Kernel A D E)
    (hK : kernelColumnsPerfect A D E K)
    [(perfectDerivedKernelAction A D E K hK).IsEquivalence]
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    DerivedModuleCategory A D ≌ DerivedModuleCategory A E := by
  have := criterionDerivedKernelIsEquivalence A D E K hK G hG H hH
  exact (kernelDerivedTensor A D E K).asEquivalence

lemma criterionDerivedKernelEquivalence_functor (K : Kernel A D E)
    (hK : kernelColumnsPerfect A D E K)
    [(perfectDerivedKernelAction A D E K hK).IsEquivalence]
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    (criterionDerivedKernelEquivalence A D E K hK G hG H hH).functor =
      kernelDerivedTensor A D E K := rfl

/-- CriterionPerf側の実際の同値の証拠を、そのまま全主導来圏同値へ拡張する。 -/
def criterionDerivedKernelEquivalenceOfPerfWitness (K : Kernel A D E)
    (W : CriterionPerfEquivalenceWitness A D E K)
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    DerivedModuleCategory A D ≌ DerivedModuleCategory A E := by
  have := W.actionIsEquivalence A D E K
  exact criterionDerivedKernelEquivalence A D E K (W.columnsPerfect A D E K) G hG H hH

lemma criterionDerivedKernelEquivalenceOfPerfWitness_functor (K : Kernel A D E)
    (W : CriterionPerfEquivalenceWitness A D E K)
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    (criterionDerivedKernelEquivalenceOfPerfWitness A D E K W G hG H hH).functor =
      kernelDerivedTensor A D E K := rfl

/-- 全導来圏同値をPerfへ制限する図式は、元の実際のPerf同値の比較を保つ。 -/
def criterionDerivedKernelEquivalenceOfPerfWitness_inclusion (K : Kernel A D E)
    (W : CriterionPerfEquivalenceWitness A D E K)
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    perfectModuleInclusion A D Set.univ ⋙
        (criterionDerivedKernelEquivalenceOfPerfWitness A D E K W G hG H hH).functor ≅
      W.equivalence.functor ⋙ perfectModuleInclusion A E Set.univ :=
  W.comparison

end SerrePositivity.DifferentialGraded.Morita
