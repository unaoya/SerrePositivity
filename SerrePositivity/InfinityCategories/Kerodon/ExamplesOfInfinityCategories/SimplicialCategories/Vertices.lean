module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaces
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：coherent nerve の零単体と元の単体的圏の対象の対応。
方針：定値豊穣関手を作り、零次の thickening の恒等が全射であることから一意性を示す。
規約：単体的圏に局所 Kan 性は要求しない。
使われ方：Kerodon §2.4.3（Tag 00KM）、Remark 3.1.6.3（Tag 01YZ）、𝒮 の頂点が表す Kan 複体の取り出し。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：単体的圏の対象を coherent nerve の零単体として表す。
方針：全ての対象を K に、全ての Hom を恒等に写す。
規約：任意の単体的圏で使い、充填性を仮定しない。
使われ方：Kerodon §2.4.3（Tag 00KM）、Remark 3.1.6.3（Tag 01YZ）、𝒮 と Cat_∞ の頂点の表示。 -/
@[kerodon 020T]
noncomputable def coherentNerveVertex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (K : C) : (SimplicialNerve C) _⦋0⦌ where
  obj _ := K
  map i j := toUnit _ ≫ eId SSet K
  map_id i := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  map_comp i j k := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app (e_id_comp SSet K K) n)
      ((eId SSet K).app n PUnit.unit)).symm

/-- 概要：零次の simplicial thickening の恒等の豊穣射は全射。
方針：零次では全ての path が同じであるため、その nerve の全単体は恒等の像。
規約：単体的圏の Hom の宇宙を u に揃える。
使われ方：Kerodon §2.4.3（Tag 00KM）、零単体の対象からの一意性。 -/
lemma thickeningZero_eId_epi (o : SimplicialThickening (ULift.{u} (Fin 1))) :
    Epi (eId SSet o) := by
  haveI : Subsingleton (SimplicialThickening.Path o.as o.as) := ⟨fun p q ↦ by
    apply SimplicialThickening.Path.ext
    ext x
    have hx : x = o.as := Subsingleton.elim _ _
    subst x
    exact iff_of_true p.left q.left⟩
  rw [NatTrans.epi_iff_epi_app]
  intro n
  rw [epi_iff_surjective]
  intro F
  refine ⟨PUnit.unit, ?_⟩
  apply CategoryTheory.Functor.ext (fun _ ↦ Subsingleton.elim _ _)

/-- 概要：coherent nerve の零単体から元の対象を取り出す。
方針：零次 thickening の唯一の対象で評価する。
規約：対象の番号は ULift した零。
使われ方：Kerodon §2.4.3（Tag 00KM）、Remark 3.1.6.3（Tag 01YZ）、fiber の値の対象の同定。 -/
def coherentNerveObject {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋0⦌) : C := s.obj ⟨ULift.up 0⟩

/-- 概要：対象を零単体にしてから取り出すと元の対象。
方針：定値豊穣関手の対象部分を評価する。
規約：通常の対象の等式。
使われ方：Kerodon §2.4.3（Tag 00KM）、coherent nerve の零単体の対応の一方向。 -/
lemma coherentNerveObject_vertex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (K : C) : coherentNerveObject (coherentNerveVertex K) = K := rfl

/-- 概要：coherent nerve の零単体はその唯一の対象から復元できる。
方針：対象の一意性と豊穣恒等からの全射性で Hom の作用を比較する。
規約：同じ対象への別の Hom の作用を許す余地がないことを証明する。
使われ方：Kerodon §2.4.3（Tag 00KM）、Remark 3.1.6.3（Tag 01YZ）、𝒮 の任意の頂点の標準表示。 -/
lemma coherentNerveVertex_object {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋0⦌) : coherentNerveVertex (coherentNerveObject s) = s := by
  let o : SimplicialThickening (ULift.{u} (Fin 1)) := ⟨ULift.up 0⟩
  have ho (i : SimplicialThickening (ULift.{u} (Fin 1))) : i = o := by
    cases i
    congr 1
    exact Subsingleton.elim _ _
  apply EnrichedFunctor.ext SSet (fun i ↦ by
    change s.obj o = s.obj i
    rw [ho i])
  intro i j
  obtain rfl := ho i
  obtain rfl := ho j
  simp only [eqToHom_refl, Category.comp_id]
  have := thickeningZero_eId_epi o
  apply (cancel_epi (eId SSet o)).1
  rw [EnrichedFunctor.map_id, s.map_id]
  rfl

/-- 概要：単体的圏の対象と coherent nerve の零単体の同値。
方針：定値豊穣関手の構成と零次 thickening での評価を組み合わせる。
規約：同型類ではなく対象の型そのものとの同値。
使われ方：Kerodon §2.4.3（Tag 00KM）、Remark 3.1.6.3（Tag 01YZ）、分類図式の値の取り出し。 -/
noncomputable def coherentNerveVertexEquiv (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    C ≃ (SimplicialNerve C) _⦋0⦌ where
  toFun := coherentNerveVertex
  invFun := coherentNerveObject
  left_inv := coherentNerveObject_vertex
  right_inv := coherentNerveVertex_object

/-- 概要：既存の 𝒮 の頂点表示は一般の coherent nerve の頂点表示と一致する。
方針：零単体をその対象から復元する一意性を使う。
規約：既存の spaceInfinityVertex の定義を変更しない。
使われ方：Kerodon Remark 3.1.6.3（Tag 01YZ）、既存の pointed space 構成との整合性。 -/
lemma spaceInfinityVertex_eq_coherent (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex K = coherentNerveVertex K :=
  (coherentNerveVertex_object (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex K)).symm

/-- 概要：𝒮 の頂点からそれが表す Kan 複体を取り出す。
方針：coherent nerve の零次 thickening での評価を使う。
規約：対象は宇宙 u の Kan 複体として取り出す。
使われ方：Kerodon Remark 3.1.6.3（Tag 01YZ）、𝒮 値図式の各頂点での値。 -/
def spaceInfinityObject (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} := coherentNerveObject s

/-- 概要：Kan 複体と 𝒮 の零単体は一対一に対応する。
方針：既存の頂点表示と coherent nerve の対象の取り出しを組み合わせる。
規約：対象の同値類ではなく KanObject 自体との同値。
使われ方：Kerodon Remark 3.1.6.3（Tag 01YZ）、fiber 比較での任意の図式の頂点の標準化。 -/
noncomputable def spaceInfinityVertexEquiv : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌ where
  toFun := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex
  invFun := spaceInfinityObject
  left_inv _ := rfl
  right_inv s := by
    rw [spaceInfinityVertex_eq_coherent]
    exact coherentNerveVertex_object s

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
