module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.ComponentProjectionDensity
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.PresentationAssembly

/-!
概要：compact comma の両成分 cofinal 性から元の compact 成分生成表示を構成する。
方針：実際の小さい filtered 全模型上の標準余錐を両成分の密度で判定する。
規約：元の対象を指定先端として保持し、全小余極限は仮定しない。
使われ方：一般 accessible 引き戻しの accessibility の最終組み立て。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：compact 入力の全余錐と両成分 cofinal 性は元の各対象の小さい filtered 表示を与える。
方針：実際の compact comma 模型上で元の標準余錐を取り、両成分で余極限性を判定する。
規約：生成表示の全図式と元の対象頂点を厳密に保持する。
使われ方：成分射影の cofinal 性の証明後に一般 accessibility を閉じる。 -/
lemma hasComponentPresentations_of_cofinal_components
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) [InnerFibration p] (hp : F1B.EquivalenceLifting p)
    (hE : IsKappaAccessible μ E) (hD : IsKappaAccessible μ D) (hB : IsKappaAccessible μ B)
    (hpμ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ p) (hqμ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ q)
    (hpCompact : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ v →
      Compact.IsKappaCompact.{u, u + 1} μ (p.app (Opposite.op ⦋0⦌) v))
    (hqCompact : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ v →
      Compact.IsKappaCompact.{u, u + 1} μ (q.app (Opposite.op ⦋0⦌) v))
    (hcone : HasCompactSliceCocones μ p q)
    (hfst : ∀ x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q,
      IsRightCofinal (componentCompactOverFst μ p q x))
    (hsnd : ∀ x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q,
      IsRightCofinal (componentCompactOverSnd μ p q x)) :
    HasComponentPresentations μ p q := by
  intro x
  let a := SSet.yonedaEquiv.symm x
  obtain ⟨M, hM, hf, ⟨e⟩⟩ :=
    exists_smallKappaFilteredComponentCommaModel_of_compactSliceCocones hμ p q hp
      hE hD hB hpCompact hqCompact hcone a
  letI := hM
  letI := hf
  let P := fun v : (sliceOver a) _⦋0⦌ ↦
    ComponentCompactVertex μ p q ((sliceOverProjection a).app (Opposite.op ⦋0⦌) v)
  let j := (fullSubcomplexOnVertices (sliceOver a) P).ι
  let T := e.hom ≫ j
  let F := T ≫ sliceOverProjection a
  let c : JoinCocone F := sliceDiagramCocone T
  have hv : c.vertex = x := by
    apply SSet.yonedaEquiv.symm.injective
    exact sliceDiagramCocone_point T
  have hF : ∀ v, ComponentCompactVertex μ p q (F.app (Opposite.op ⦋0⦌) v) := by
    intro v
    exact fullSubcomplexOnVertices_vertex (e.hom.app (Opposite.op ⦋0⦌) v)
  have hcf : IsColimitCone (mapJoinCocone (pullback.fst p q) c) :=
    componentCanonicalCocone_image_isColimit_of_isRightCofinal hμ p q hE
      (pullback.fst p q) a e (componentCompactOverFst μ p q a)
      (componentCompactOverFst_inclusion μ p q a) (hfst a)
  have hcs : IsColimitCone (mapJoinCocone (pullback.snd p q) c) :=
    componentCanonicalCocone_image_isColimit_of_isRightCofinal hμ p q hD
      (pullback.snd p q) a e (componentCompactOverSnd μ p q a)
      (componentCompactOverSnd_inclusion μ p q a) (hsnd a)
  have hc : IsColimitCone c :=
    (pullback_filtered_isColimitCone_iff_components p q hp
      hE.hasSmallKappaFilteredColimits hD.hasSmallKappaFilteredColimits hpμ hqμ c).mpr ⟨hcf, hcs⟩
  exact ⟨M, hM, hf, F, hF, c, hc, hv⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
