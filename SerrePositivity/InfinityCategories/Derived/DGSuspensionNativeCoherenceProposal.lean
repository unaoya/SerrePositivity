module
public import SerrePositivity.InfinityCategories.Derived.DGSuspensionNativeSquareModel
public import SerrePositivity.InfinityCategories.Core.RelativeEquivalencePathAt
public import SerrePositivity.InfinityCategories.Core.VertexDiscrete
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeEquivalencePathExtension

/-!
概要：固定懸垂作用の厳密豊穣供給に対する、未採用の二つの緩和案を型として示す。
方針：元の vertex と実射データを保つ案と、関手的補助模型から指定同値で戻る案を区別する。
規約：既存の KST 型・模型・I・P を変更しない。存在や緩和の採用は主張しない。
使われ方：ユーザー経由の設計判断と K-B3 の影響評価。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction SerrePositivity.KST.NonConnective
namespace SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ)

/-- 元の厳密 vertex 等号だけで正規化した、全作用の実際の dg 入力辺。 -/
def dgSuspensionMappedEdge
    (m : dgKInputInfinity.{u, max (u + 1) v} R ⟶ dgKInputInfinity.{u, max (u + 1) v} R)
    (hv : ∀ A : PerfDGInput.{u, max (u + 1) v} R,
      m.app (Opposite.op ⦋0⦌) (coherentNerveVertex A) =
        coherentNerveVertex (dgKappaSuspensionKInput R A (s A).cone))
    {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) :
    SSet.Edge (coherentNerveVertex (dgKappaSuspensionKInput R A (s A).cone))
      (coherentNerveVertex (dgKappaSuspensionKInput R B (s B).cone)) :=
  ((coherentNerveEdge f).map m).ofEq (hv A) (hv B)

/-- 案 B1：vertex は厳密、各元の dg 射との照合は端点固定の指定可逆二胞体。未採用。 -/
structure DGSuspensionCoherentActionProposal where
  map : dgKInputInfinity.{u, max (u + 1) v} R ⟶ dgKInputInfinity.{u, max (u + 1) v} R
  vertex : ∀ A : PerfDGInput.{u, max (u + 1) v} R,
    map.app (Opposite.op ⦋0⦌) (coherentNerveVertex A) =
      coherentNerveVertex (dgKappaSuspensionKInput R A (s A).cone)
  data : ∀ {A B : PerfDGInput.{u, max (u + 1) v} R}, (A ⟶ B) →
    DGKappaSuspensionMapData R A B (s A).cone (s B).cone
  /-- 固定端点の写像空間内の同型なので、両端の成分は動かない。 -/
  edgeIso : ∀ {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B),
    VertexIso (intervalMappingVertexOfEdge (dgSuspensionMappedEdge R s map vertex f))
      (intervalMappingVertexOfEdge (coherentNerveEdge
        (dgKappaSuspensionInputMap R A B (s A).cone (s B).cone (data f))))

/-- 元の厳密作用は、データを変えずに案 B1 を満たす。 -/
def DGSuspensionCoherentActionProposal.ofStrict (a : DGSuspensionNativeActionInput R s) :
    DGSuspensionCoherentActionProposal R s where
  map := a.map
  vertex := a.vertex
  data := a.data
  edgeIso f := by
    have h : dgSuspensionMappedEdge R s a.map a.vertex f =
        coherentNerveEdge
          (dgKappaSuspensionInputMap R _ _ _ _ (a.data f)) := by
      apply SSet.Edge.ext
      exact a.edge f
    rw [h]

/-- 案 B1 の全四角形。豊穣関手の三フィールドを要求せず、元の全四角形一致を保つ。 -/
structure DGSuspensionCoherentSquareProposal where
  action : DGSuspensionCoherentActionProposal R s
  square : ((Δ[1] ⊗ Δ[1]) ⊗ dgKInputInfinity.{u, max (u + 1) v} R) ⟶
    dgKInputInfinity.{u, max (u + 1) v} R
  square_at : ∀ A : PerfDGInput.{u, max (u + 1) v} R,
    dgSuspensionNativeSquareAt R square A = dgKappaResolvedConnectiveSquare R A (s A).cone
  suspension : dgSuspensionNativeSquareCornerFamily R square 1 1 = action.map

/-- 案 B2：関手的補助構成の厳密豊穣作用と、同じ固定懸垂への全 native 自然な同値。
比較は固定源 S 内。Morita 同値や ν/K の像だけの同値では代用しない。未採用。 -/
structure DGSuspensionFunctorialComparisonProposal where
  enriched : EnrichedFunctor SSet.{max (u + 1) v}
    (PerfDGInput.{u, max (u + 1) v} R) (PerfDGInput.{u, max (u + 1) v} R)
  comparison : dgKInputInfinity.{u, max (u + 1) v} R ⟶
    equivalencePath (dgKInputInfinity.{u, max (u + 1) v} R)
  comparison_source : comparison ≫ equivalencePathEndpoint _ 0 = coherentNerveMap enriched
  comparison_target_at : ∀ A : PerfDGInput.{u, max (u + 1) v} R,
    (comparison ≫ equivalencePathEndpoint _ 1).app (Opposite.op ⦋0⦌) (coherentNerveVertex A) =
      coherentNerveVertex (dgKappaSuspensionKInput R A (s A).cone)

variable (p : DGSuspensionFunctorialComparisonProposal R s)

/-- 補助構成と比較から得る、元の固定 vertex を持つ全 coherent 作用。 -/
def DGSuspensionFunctorialComparisonProposal.map :
    dgKInputInfinity.{u, max (u + 1) v} R ⟶ dgKInputInfinity.{u, max (u + 1) v} R :=
  p.comparison ≫ equivalencePathEndpoint _ 1

/-- 比較は全 native 入力上の関手同型である。対象別同値だけの型ではない。 -/
def DGSuspensionFunctorialComparisonProposal.comparisonIso :
    FunctorIso (coherentNerveMap p.enriched) (p.map R s) := by
  have h := F1B.kanEquivalencePath_functorIso p.comparison
  rw [p.comparison_source] at h
  exact h

/-- 厳密豊穣な補助作用がある場合、固定源 S 内の点別同値から全比較を構成できる。
この結果は、戻した固定対象作用に厳密豊穣単位・合成則を主張しない。 -/
lemma dgSuspensionFunctorialComparisonProposal_exists
    (F : EnrichedFunctor SSet.{max (u + 1) v}
      (PerfDGInput.{u, max (u + 1) v} R) (PerfDGInput.{u, max (u + 1) v} R))
    (e : PerfDGInput.{u, max (u + 1) v} R →
      (equivalencePath (dgKInputInfinity.{u, max (u + 1) v} R)) _⦋0⦌)
    (he₀ : ∀ A, (equivalencePathEndpoint _ 0).app (Opposite.op ⦋0⦌) (e A) =
      coherentNerveVertex (F.obj A))
    (he₁ : ∀ A, (equivalencePathEndpoint _ 1).app (Opposite.op ⦋0⦌) (e A) =
      coherentNerveVertex (dgKappaSuspensionKInput R A (s A).cone)) :
    ∃ p : DGSuspensionFunctorialComparisonProposal R s,
      p.enriched = F ∧ ∀ A, p.comparison.app (Opposite.op ⦋0⦌) (coherentNerveVertex A) = e A := by
  let a := fun k : (dgKInputInfinity.{u, max (u + 1) v} R) _⦋0⦌ => e (coherentNerveObject k)
  have ha : ∀ k, (equivalencePathEndpoint _ 0).app (Opposite.op ⦋0⦌) (a k) =
      (coherentNerveMap F).app (Opposite.op ⦋0⦌) k := by
    intro k
    obtain ⟨A, rfl⟩ := (coherentNerveVertexEquiv
      (PerfDGInput.{u, max (u + 1) v} R)).surjective k
    change (equivalencePathEndpoint _ 0).app (Opposite.op ⦋0⦌)
      (e (coherentNerveObject (coherentNerveVertex A))) =
        (coherentNerveMap F).app (Opposite.op ⦋0⦌) (coherentNerveVertex A)
    rw [coherentNerveObject_vertex, coherentNerveMap_vertex]
    exact he₀ A
  have : HasLiftingProperty (vertexDiscreteι (dgKInputInfinity.{u, max (u + 1) v} R))
      (equivalencePathEndpoint (dgKInputInfinity.{u, max (u + 1) v} R) 0) :=
    TrivialKanFibration.mem _ inferInstance
  let sq : CommSq (vertexDiscreteMap a) (vertexDiscreteι _)
      (equivalencePathEndpoint _ 0) (coherentNerveMap F) :=
    ⟨vertexDiscreteMap_comp _ _ a ha⟩
  have hv (A : PerfDGInput.{u, max (u + 1) v} R) :
      sq.lift.app (Opposite.op ⦋0⦌) (coherentNerveVertex A) = e A := by
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app sq.fac_left (Opposite.op ⦋0⦌)) (coherentNerveVertex A)
    change sq.lift.app (Opposite.op ⦋0⦌) (PinchedHom.constant (coherentNerveVertex A) 0) =
      PinchedHom.constant (a (coherentNerveVertex A)) 0 at h
    simpa only [pinchedConstant_zero, a, coherentNerveObject_vertex] using h
  refine ⟨⟨F, sq.lift, sq.fac_right, ?_⟩, rfl, hv⟩
  intro A
  change (equivalencePathEndpoint _ 1).app (Opposite.op ⦋0⦌)
    (sq.lift.app (Opposite.op ⦋0⦌) (coherentNerveVertex A)) = _
  rw [hv]
  exact he₁ A

end SerrePositivity.InfinityCategories
