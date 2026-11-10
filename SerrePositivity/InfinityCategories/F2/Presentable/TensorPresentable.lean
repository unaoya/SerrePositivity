module

public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafTensorPresentable
public import SerrePositivity.InfinityCategories.F2.Presentable.TensorAccessibility
public import SerrePositivity.InfinityCategories.F2.Presentable.FunctorIsoTensor
public import SerrePositivity.InfinityCategories.F2.Presentable.IndPresheafReflection
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaSmallness

/-!
概要：二つの presentable 圏の元の二項積は presentable。
方針：前層反映の二項積から小さい compact 生成模型を構成し、元の同値で戻す。
規約：随伴関手定理や一般 Bousfield 局所化の存在を使わない。
使われ方：Pr^L の積と小極限の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
attribute [local instance] F2.quasicategory_tensor

/-- 概要：元の全同値の二項積は元の二項積の全同値。
方針：両逆射と全可逆二胞体を二項積にする。
規約：指定した元の全同値を使う。使われ方：反映 Ind 模型から積への移送。 -/
def qCatEquivalenceTensor {C D E F : SSet.{u + 1}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E] [Quasicategory F]
    (e : QCatEquivalence C D) (f : QCatEquivalence E F) :
    QCatEquivalence (C ⊗ E) (D ⊗ F) where
  hom := e.hom ⊗ₘ f.hom
  inv := e.inv ⊗ₘ f.inv
  homInvIso := tensorReflectionCounitIso e.homInvIso f.homInvIso
  invHomIso := tensorReflectionCounitIso e.invHomIso f.invHomIso

/-- 概要：二つの余完備な Ind 模型の元の二項積は presentable。
方針：前層圏の二項積の反映に、右随伴の filtered 保存を適用する。
規約：元の二つの正則濃度は異なってよい。
使われ方：一般 presentable 圏の二項積の模型。 -/
lemma indTensor_isPresentable (A B : SSet.{u}) [Quasicategory A] [Quasicategory B]
    (κ ν : Cardinal.{u}) [Fact κ.IsRegular] [Fact ν.IsRegular]
    (hA : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (Ind.IndInfinity κ A))
    (hB : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (Ind.IndInfinity ν B)) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (Ind.IndInfinity κ A ⊗ Ind.IndInfinity ν B) := by
  let r := indPresheafReflection hA
  let s := indPresheafReflection hB
  have hcol := tensor_hasSmallColimits hA hB
  have hs := tensor_hasSmallFixedVertexMaps
    (Ind.ind_hasSmallFixedVertexMaps κ A) (Ind.ind_hasSmallFixedVertexMaps ν B)
  obtain ⟨μ, hκνμ, hμ⟩ := (presheafTensor_isPresentable A B).isAccessible.exists_larger (max κ ν)
  have hκμ : κ ≤ μ := (le_max_left κ ν).trans hκνμ.le
  have hνμ : ν ≤ μ := (le_max_right κ ν).trans hκνμ.le
  have hrκ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (Ind.indInclusionPresheaf κ A) :=
    Ind.indInclusion_preservesSmallKappaFilteredColimits κ A
  have htν : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor ν (Ind.indInclusionPresheaf ν B) :=
    Ind.indInclusion_preservesSmallKappaFilteredColimits ν B
  have hr := hrκ.of_le hκμ
  have ht := htν.of_le hνμ
  have hR := tensorHom_isKappaAccessible hA hB
    (_root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presheaf_hasSmallColimits A) (_root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presheaf_hasSmallColimits B) hr ht
  have he : FunctorIso
      ((Ind.indInclusionPresheaf κ A ⊗ₘ Ind.indInclusionPresheaf ν B) ≫
        (r.reflector ⊗ₘ s.reflector))
      (𝟙 (Ind.IndInfinity κ A ⊗ Ind.IndInfinity ν B)) := by
    simpa only [Ind.indInclusionPresheaf, Ind.IndInfinity] using
      tensorReflectionCounitIso r.counitIso s.counitIso
  exact ⟨(reflectiveImage_isKappaAccessible (tensorAdjunction r.adjunction s.adjunction)
    he hμ hcol hs hR).isAccessible, hcol⟩

/-- 概要：二つの presentable 圏の元の二項積は presentable。
方針：各元の反映 Ind 模型の積を全同値で戻す。
規約：宇宙比較や交換定理の存在入力を追加しない。
使われ方：Pr^L の二項積。 -/
lemma tensor_isPresentable {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable D) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (C ⊗ D) := by
  obtain ⟨κ, hκ, A, hA, _, ⟨e⟩⟩ := hC.exists_reflectiveIndModel
  obtain ⟨ν, hν, B, hB, _, ⟨f⟩⟩ := hD.exists_reflectiveIndModel
  have := hA
  have := hB
  have : Fact κ.IsRegular := ⟨hκ⟩
  have : Fact ν.IsRegular := ⟨hν⟩
  exact (indTensor_isPresentable A B κ ν
    (hC.hasSmallColimits.of_equivalence e.symm)
    (hD.hasSmallColimits.of_equivalence f.symm)).of_equivalence (qCatEquivalenceTensor e f)

end SerrePositivity.InfinityCategories.F2.Presentable
