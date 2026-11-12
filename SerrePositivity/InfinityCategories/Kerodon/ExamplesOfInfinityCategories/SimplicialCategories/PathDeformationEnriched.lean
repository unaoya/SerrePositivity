module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathDeformation

/-!
概要：時刻付き path の変形による simplicial thickening 間の豊穣関手。
方針：path の包含の関手の nerve を Hom の作用とし、集合の合成則を使う。
規約：対象の射は時刻に依存せず、Hom の作用だけを変形する。
使われ方：Kerodon §5.6（Tag 027M）、coherent な単体と strict な射列の間の比較。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：時刻付き path の変形は端点間の path の圏の関手。
方針：path の包含を変形後の包含に送る。
規約：始域の二端点 i と j は固定。
使われ方：Kerodon §2.4.3（Tag 00KM）、豊穣 Hom の作用を nerve として構成する。 -/
def coherentPathDeformationFunctor {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) (i j : J) : Path i j ⥤ Path (A i) (A j) where
  obj P := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformation A t P
  map f := ⟨⟨⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformation_mono A t f.1.1.1⟩⟩⟩

/-- 概要：時刻付き path の変形は simplicial thickening の豊穣関手。
方針：path の関手の nerve を Hom に作用させ、恒等と合成を各 path で確認する。
規約：対象は A で写し、Hom の時刻依存は t による。
使われ方：Kerodon §5.6（Tag 027M）、単体の prism 上で coherent な図式を組み立てる。 -/
def coherentPathDeformationEnriched {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) (t : J →o Fin 2) :
    EnrichedFunctor SSet.{u} (SimplicialThickening J) (SimplicialThickening K) where
  obj i := ⟨A i.as⟩
  map i j := nerveMap (coherentPathDeformationFunctor A t i.as j.as)
  map_id i := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    apply CategoryTheory.Functor.ext (fun _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformation_id A t i.as)
  map_comp i j k := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    apply CategoryTheory.Functor.ext
      (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformation_comp A t (P.obj z) (Q.obj z))

/-- 概要：変形の豊穣関手は始域の単調写像による前合成と可換。
方針：全ての path の添字変換の式を Hom の各次数へ適用する。
規約：対象での等式は定義的。
使われ方：Kerodon §5.6（Tag 027M）、prism の図式の面・退化との整合性。 -/
lemma coherentPathDeformationEnriched_reindex {I J K : Type u}
    [LinearOrder I] [LinearOrder J] [LinearOrder K]
    (g : I →o J) (A : J →o K) (t : J →o Fin 2) :
    (SimplicialThickening.functor g).comp SSet (coherentPathDeformationEnriched A t) =
      coherentPathDeformationEnriched (A.comp g) (t.comp g) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext
    (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformation_reindex g A t (P.obj z)).symm)

/-- 概要：時刻零の変形の豊穣関手は元の単調写像の豊穣表示。
方針：追加区間が空になる path の式を各 Hom の nerve に適用する。
規約：順序集合の射 A は任意。
使われ方：Kerodon §5.6（Tag 027M）、coherent な単体の変形の初期値。 -/
lemma coherentPathDeformationEnriched_zero {J K : Type u} [LinearOrder J] [LinearOrder K]
    (A : J →o K) :
    coherentPathDeformationEnriched A (OrderHom.const J 0) = SimplicialThickening.functor A := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformation_zero A (P.obj z))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
