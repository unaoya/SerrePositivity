module

public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafSigmaBase
public import SerrePositivity.InfinityCategories.F2.Presentable.PiAccessibility
public import SerrePositivity.InfinityCategories.F2.Presentable.PiAdjunction
public import SerrePositivity.InfinityCategories.F2.Presentable.PiFunctorIso
public import SerrePositivity.InfinityCategories.F2.Presentable.IndPresheafReflection
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaSmallness

/-!
概要：presentable 圏の任意の小さい全直積は presentable。
方針：各前層反映の全直積から共通濃度の小さい compact 生成模型を構成する。
規約：随伴関手定理や一般局所化の存在を使わず、元の積を保持する。
使われ方：Pr^L の小さい積と小極限の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：余完備な Ind 模型の小さい族の元の全直積は presentable。
方針：前層圏族の反映の全直積に共通の filtered 保存濃度を取り、生成対象を反映する。
規約：各成分の元の正則濃度は異なってよい。
使われ方：一般 presentable 圏の小さい積の模型。 -/
lemma piInd_isPresentable {ι : Type u} (A : ι → SSet.{u})
    [∀ i, Quasicategory (A i)] (κ : ι → Cardinal.{u}) [∀ i, Fact (κ i).IsRegular]
    (hI : ∀ i, _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (Ind.IndInfinity (κ i) (A i))) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (piSSet (fun i ↦ Ind.IndInfinity (κ i) (A i))) := by
  let r (i : ι) := indPresheafReflection (hI i)
  have hcol := piSSet_hasSmallColimits hI
  have hs := piSSet_hasSmallFixedVertexMaps
    (fun i ↦ Ind.ind_hasSmallFixedVertexMaps (κ i) (A i))
  obtain ⟨θ, hθ⟩ := Cardinal.exists_le_of_small κ
  obtain ⟨μ, hθμ, hμ⟩ := (piPresheaf_isPresentable A).isAccessible.exists_larger θ
  have hr (i : ι) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor (κ i)
      (Ind.indInclusionPresheaf (κ i) (A i)) :=
    Ind.indInclusion_preservesSmallKappaFilteredColimits (κ i) (A i)
  have hR := piSSetMap_isKappaAccessible hI (fun i ↦ _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presheaf_hasSmallColimits (A i))
    (fun i ↦ (hr i).of_le ((hθ i).trans hθμ.le))
  have he : FunctorIso
      (piSSetMap (fun i ↦ Ind.indInclusionPresheaf (κ i) (A i)) ≫
        piSSetMap (fun i ↦ (r i).reflector))
      (𝟙 (piSSet (fun i ↦ Ind.IndInfinity (κ i) (A i)))) := by
    simpa only [Ind.indInclusionPresheaf, Ind.IndInfinity] using
      piReflectionCounitIso (fun i ↦ (r i).counitIso)
  exact ⟨(reflectiveImage_isKappaAccessible (piAdjunction (fun i ↦ (r i).adjunction))
    he hμ hcol hs hR).isAccessible, hcol⟩

/-- 概要：presentable 圏の任意の小さい族の元の全直積は presentable。
方針：各反映 Ind 模型の全直積を作り、元の全同値の直積で戻す。
規約：空の添字も含め、濃度や交換定理の追加仮定を置かない。
使われ方：Pr^L の小さい積。 -/
lemma piSSet_isPresentable {ι : Type u} {C : ι → SSet.{u + 1}}
    [∀ i, Quasicategory (C i)] (hC : ∀ i, _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (C i)) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (piSSet C) := by
  choose κ hκ A hA hr he using fun i ↦ (hC i).exists_reflectiveIndModel
  have : ∀ i, Quasicategory (A i) := hA
  have : ∀ i, Fact (κ i).IsRegular := fun i ↦ ⟨hκ i⟩
  let e (i : ι) : QCatEquivalence (Ind.IndInfinity (κ i) (A i)) (C i) :=
    Classical.choice (he i)
  exact (piInd_isPresentable A κ
    (fun i ↦ (hC i).hasSmallColimits.of_equivalence (e i).symm)).of_equivalence
      (qCatEquivalencePi e)

end SerrePositivity.InfinityCategories.F2.Presentable
