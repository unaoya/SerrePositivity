module

public import SerrePositivity.InfinityCategories.Core.InternalHomSwap
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexIso
public import SerrePositivity.InfinityCategories.Core.EquivalencePathMap

/-!
概要：関手単体集合の可逆な path と可逆な path の関手単体集合の比較。
方針：二重の内部 Hom を交換し、辺の可逆性の点ごとの判定で全部分複体を対応させる。
規約：標的 X のみ quasicategory とする。
使われ方：Kerodon §4.5.3、§4.5.5 の制限の相対 path の持ち上げ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：関手単体集合の任意の両端を持つ辺の可逆性は点ごとに判定される。
方針：両端の頂点を実際の関手で表して既存の判定を使う。
規約：K は任意、X は quasicategory。
使われ方：Kerodon §4.5.3 の可逆 path の全部分複体の条件。 -/
lemma isInvertibleEdge_iff_evaluateFunctorAt_any {K X : SSet.{u}} [Quasicategory X]
    {v w : ((ihom K).obj X) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X)) v w) :
    IsInvertibleEdge e ↔ ∀ k : K _⦋0⦌,
      IsInvertibleEdge (e.map ((truncation 2).map (evaluateFunctorAt (Y := X) k))) := by
  obtain ⟨f, rfl⟩ := (functorVertexEquiv K X).surjective v
  obtain ⟨g, rfl⟩ := (functorVertexEquiv K X).surjective w
  exact isInvertibleEdge_iff_evaluateFunctorAt e

/-- 概要：関手単体集合の可逆 path は可逆 path の関手単体集合と同型。
方針：内部 Hom の交換の同型に点ごとの可逆性を使って全部分複体を対応させる。
規約：X の quasicategory 性だけを仮定する。
使われ方：Kerodon §4.5.3、§4.5.5 の相対 path の持ち上げ。 -/
noncomputable def equivalencePathInternalHomIso (K X : SSet.{u}) [Quasicategory X] :
    equivalencePath ((ihom K).obj X) ≅ (ihom K).obj (equivalencePath X) :=
  fullSubcomplexIso (internalHomSwapIso Δ[1] K X) IsEquivalencePathVertex
    (FunctorVertexSatisfies K ((ihom (Δ[1] : SSet.{u})).obj X) IsEquivalencePathVertex)
    (by
      intro v
      change IsInvertibleEdge (edgeOfSimplex (intervalFunctorVertexEdge v)) ↔ _
      refine (isInvertibleEdge_iff_evaluateFunctorAt_any
        (edgeOfSimplex (intervalFunctorVertexEdge v))).trans ?_
      apply forall_congr'
      intro k
      exact (isInvertibleEdge_congr (internalHomSwapIso_interval_evaluate K X v k)).symm) ≪≫
    (fullSubcomplexInternalHomIso K ((ihom (Δ[1] : SSet.{u})).obj X)
      IsEquivalencePathVertex).symm

/-- 概要：可逆 path と内部 Hom の比較は、条件を忘れると内部 Hom の交換になる。
方針：二つの全部分複体の比較の包含上の等式を使う。
規約：同型の順方向についての等式。
使われ方：Kerodon §4.5.3 の両端の自然性。 -/
lemma equivalencePathInternalHomIso_hom_ι (K X : SSet.{u}) [Quasicategory X] :
    (equivalencePathInternalHomIso K X).hom ≫ (ihom K).map (equivalencePathι X) =
      equivalencePathι ((ihom K).obj X) ≫ (internalHomSwapIso Δ[1] K X).hom := by
  unfold equivalencePathι
  dsimp only [equivalencePathInternalHomIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, fullSubcomplexInternalHomIso_inv_ι, fullSubcomplexIso_hom_ι]

/-- 概要：可逆 path と内部 Hom の比較は両端の評価を保つ。
方針：条件を忘れた交換の同型と評価の等式を使う。
規約：両端 i は任意。
使われ方：Kerodon §4.5.5 の制限に対する相対 path。 -/
lemma equivalencePathInternalHomIso_endpoint (K X : SSet.{u}) [Quasicategory X] (i : Fin 2) :
    (equivalencePathInternalHomIso K X).hom ≫ (ihom K).map (equivalencePathEndpoint X i) =
      equivalencePathEndpoint ((ihom K).obj X) i := by
  change (equivalencePathInternalHomIso K X).hom ≫
    (ihom K).map (equivalencePathι X ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i)) = _
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc,
    equivalencePathInternalHomIso_hom_ι, Category.assoc, internalHomSwapIso_evaluate]
  rfl

/-- 概要：可逆 path と内部 Hom の比較は始域の制限と可換。
方針：全部分複体の包含で比較し、内部 Hom の交換の自然性を使う。
規約：i は任意の射、X は quasicategory。
使われ方：Kerodon §4.5.5 の制限の相対 path の持ち上げ。 -/
lemma equivalencePathInternalHomIso_pre {A B X : SSet.{u}} [Quasicategory X] (i : A ⟶ B) :
    equivalencePathMap ((pre i).app X) ≫ (equivalencePathInternalHomIso A X).hom =
      (equivalencePathInternalHomIso B X).hom ≫ (pre i).app (equivalencePath X) := by
  have : Mono (equivalencePathι X) := by unfold equivalencePathι; infer_instance
  have : Mono ((ihom A).map (equivalencePathι X)) := (ihom A).map_mono _
  apply (cancel_mono ((ihom A).map (equivalencePathι X))).1
  have hn := (pre i).naturality (equivalencePathι X)
  calc
    (equivalencePathMap ((pre i).app X) ≫ (equivalencePathInternalHomIso A X).hom) ≫
        (ihom A).map (equivalencePathι X) =
      equivalencePathMap ((pre i).app X) ≫
        (equivalencePathι ((ihom A).obj X) ≫ (internalHomSwapIso Δ[1] A X).hom) := by
      rw [Category.assoc, equivalencePathInternalHomIso_hom_ι]
    _ = (equivalencePathι ((ihom B).obj X) ≫ (ihom (Δ[1] : SSet.{u})).map ((pre i).app X)) ≫
        (internalHomSwapIso Δ[1] A X).hom := by
      rw [← Category.assoc, equivalencePathMap_ι]
    _ = equivalencePathι ((ihom B).obj X) ≫
        ((internalHomSwapIso Δ[1] B X).hom ≫ (pre i).app ((ihom (Δ[1] : SSet.{u})).obj X)) := by
      rw [Category.assoc, internalHomSwapIso_pre]
    _ = ((equivalencePathInternalHomIso B X).hom ≫ (ihom B).map (equivalencePathι X)) ≫
        (pre i).app ((ihom (Δ[1] : SSet.{u})).obj X) := by
      rw [equivalencePathInternalHomIso_hom_ι, Category.assoc]
    _ = ((equivalencePathInternalHomIso B X).hom ≫ (pre i).app (equivalencePath X)) ≫
        (ihom A).map (equivalencePathι X) := by
      rw [Category.assoc, hn, ← Category.assoc]

end SerrePositivity.InfinityCategories
