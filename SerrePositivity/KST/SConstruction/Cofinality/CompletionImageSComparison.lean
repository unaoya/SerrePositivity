module
public import SerrePositivity.KST.SConstruction.Cofinality.CompletionImageEquivalence
public import SerrePositivity.KST.SConstruction.Cofinality.MultiDiagramImage
public import SerrePositivity.KST.SConstruction.SClosedStableIso

/-!
概要：指定完備化射の本質像条件と、S 構成の全成分の像条件を照合する。
方針：完全な Ar 評価の自然性と、同じ S_n 内の全図式回収を使う。
規約：各成分の像条件から全図式を同時に回収し、射を別の同値へ置き換えない。
使われ方：K-B2-S1 の本質像入力と全 S 多次数の交換。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：一方向の S 上の本質像条件は全 Ar 成分の元の本質像条件に等しい。
方針：同型を各 Ar 評価で写し、逆向きは元の S_n 射への同時回収を使う。
規約：全多次数にさらに一方向を加えた元の指定射を使う。
使われ方：本質像の閉じた安定条件と S 構成との交換。 -/
lemma completionImage_sClosedPredicate_iff (n r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (v : (sConstruction n (((multiSEndofunctor r).obj ι).obj Y).carrier) _⦋0⦌) :
    (sClosedPredicate n (completionImageClosedPredicate r ι f hf)).predicate v ↔
      ∃ x : (sConstruction n (((multiSEndofunctor r).obj ι).obj X).carrier) _⦋0⦌,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (((sEndofunctor n).map
          (((multiSEndofunctor r).obj ι).map f)).val.app (Opposite.op ⦋0⦌) x) v) := by
  let F := ((multiSEndofunctor r).obj ι).map f
  constructor
  · intro hv
    apply exists_sVertexIso_of_pointwise_image F
      (multiSEndofunctor_map_isIdempotentCompletion r ι f hf).2.1 v
    intro a
    have h := hv a
    change ∃ x, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (F.val.app (Opposite.op ⦋0⦌) x)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a).app (Opposite.op ⦋0⦌) v.val)) at h
    exact (functorVertexEquiv_symm_evaluate v.val a).symm ▸ h
  · rintro ⟨x, ⟨e⟩⟩ a
    have ei := e.map (sStableEvaluation n (((multiSEndofunctor r).obj ι).obj Y) a).val
    have hs := congrArg (fun q : sStableModel n (((multiSEndofunctor r).obj ι).obj X) ⟶
        ((multiSEndofunctor r).obj ι).obj Y => q.val.app (Opposite.op ⦋0⦌) x)
      (sStableEvaluation_naturality n F a)
    refine ⟨(sStableEvaluation n (((multiSEndofunctor r).obj ι).obj X) a).val.app
      (Opposite.op ⦋0⦌) x, ⟨?_⟩⟩
    exact hs ▸ ei

/-- 概要：全反復 S の元の本質像は全ての入れ子 Ar 成分の本質像条件に等しい。
方針：一方向の交換を反復数について帰納し、全図式の像を同時に回収する。
規約：全多次数を独立に保ち、対角上だけの条件へ弱めない。
使われ方：元の本質像を全 S 多次数の共通供給へ代入する際の判定。 -/
theorem completionImage_multiPointwise_iff (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (v : ((((multiSEndofunctor r).obj ι).obj Y).carrier) _⦋0⦌) :
    MultiPointwiseImage f r ι v ↔
      (completionImageClosedPredicate r ι f hf).predicate v := by
  induction r with
  | zero => exact Iff.rfl
  | succ r ih =>
    let d := fun i : Fin r => ι i.succ
    change (∀ a : (arNerve (ι 0).unop.len) _⦋0⦌,
      MultiPointwiseImage f r d ((gappedDiagram v).app (Opposite.op ⦋0⦌) a)) ↔ _
    have hpoint : (∀ a : (arNerve (ι 0).unop.len) _⦋0⦌,
        MultiPointwiseImage f r d ((gappedDiagram v).app (Opposite.op ⦋0⦌) a)) ↔
        (sClosedPredicate (ι 0).unop.len
          (completionImageClosedPredicate r d f hf)).predicate v := by
      apply forall_congr'
      intro a
      exact (ih d _).trans (Iff.of_eq (congrArg
        (completionImageClosedPredicate r d f hf).predicate
          (functorVertexEquiv_symm_evaluate v.val a)))
    exact hpoint.trans (completionImage_sClosedPredicate_iff (ι 0).unop.len r d f hf v)

/-- 概要：本質像の閉条件は一方向の S 構成と厳密に交換する。
方針：全 Ar 成分の判定の同値を predicate の等号へ移す。
規約：閉性の証明成分には証明の無関係性だけを使う。
使われ方：閉じた本質像の模型と S 模型の厳密な照合。 -/
lemma completionImage_sClosedPredicate_eq (n r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    sClosedPredicate n (completionImageClosedPredicate r ι f hf) =
      completionImageClosedPredicate (r + 1) (Fin.cons (Opposite.op ⦋n⦌) ι) f hf := by
  have hp : (sClosedPredicate n (completionImageClosedPredicate r ι f hf)).predicate =
      (completionImageClosedPredicate (r + 1) (Fin.cons (Opposite.op ⦋n⦌) ι) f hf).predicate :=
    funext (fun v => propext (completionImage_sClosedPredicate_iff n r ι f hf v))
  generalize sClosedPredicate n (completionImageClosedPredicate r ι f hf) = P at *
  generalize completionImageClosedPredicate (r + 1) (Fin.cons (Opposite.op ⦋n⦌) ι) f hf = Q at *
  cases P
  cases Q
  dsimp only at hp
  cases hp
  rfl

/-- 概要：閉じた本質像の S 模型は、次の多次数の本質像の安定模型と同型。
方針：既存の全部分圏との S 交換同型を、元の本質像条件の等号で移す。
規約：一方向を加えた元の指定射の本質像を使う。
使われ方：K-B2-S1 への入力を全 S 多次数へ移す交換同型。 -/
def completionImageSStableIso (n r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    sStableModel n (closedStableModel (completionImageClosedPredicate r ι f hf)) ≅
      closedStableModel (completionImageClosedPredicate (r + 1)
        (Fin.cons (Opposite.op ⦋n⦌) ι) f hf) :=
  sClosedStableIso n (completionImageClosedPredicate r ι f hf) ≪≫
    eqToIso (congrArg (fun P : ClosedStablePredicate
      (sStableModel n (((multiSEndofunctor r).obj ι).obj Y)) => closedStableModel P)
        (completionImage_sClosedPredicate_eq n r ι f hf))

end SerrePositivity.KST.SConstruction.Cofinality
