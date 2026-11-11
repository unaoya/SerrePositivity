module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InternalHomSwap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FullSubcomplexIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathMap
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：関手単体集合の可逆な path と可逆な path の関手単体集合の比較。
方針：二重の内部 Hom を交換し、辺の可逆性の点ごとの判定で全部分複体を対応させる。
規約：標的 X のみ quasicategory とする。
使われ方：Kerodon §4.5.3（Tag 032Y）、§4.5.5（Tag 01F6） の制限の相対 path の持ち上げ。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：関手単体集合の任意の両端を持つ辺の可逆性は点ごとに判定される。
方針：両端の頂点を実際の関手で表して既存の判定を使う。
規約：K は任意、X は quasicategory。
使われ方：Kerodon §4.5.3（Tag 032Y） の可逆 path の全部分複体の条件。 -/
@[kerodon 01DK]
lemma isInvertibleEdge_iff_evaluateFunctorAt_any {K X : SSet.{u}} [Quasicategory X]
    {v w : ((ihom K).obj X) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X)) v w) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e ↔ ∀ k : K _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k))) := by
  obtain ⟨f, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K X).surjective v
  obtain ⟨g, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K X).surjective w
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt e

/-- 概要：関手単体集合の可逆 path は可逆 path の関手単体集合と同型。
方針：内部 Hom の交換の同型に点ごとの可逆性を使って全部分複体を対応させる。
規約：X の quasicategory 性だけを仮定する。
使われ方：Kerodon §4.5.3（Tag 032Y）、§4.5.5（Tag 01F6） の相対 path の持ち上げ。 -/
noncomputable def equivalencePathInternalHomIso (K X : SSet.{u}) [Quasicategory X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath ((ihom K).obj X) ≅ (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso Δ[1] K X) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorVertexSatisfies K ((ihom (Δ[1] : SSet.{u})).obj X) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex)
    (by
      intro v
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge v)) ↔ _
      refine (isInvertibleEdge_iff_evaluateFunctorAt_any
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge v))).trans ?_
      apply forall_congr'
      intro k
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_interval_evaluate K X v k)).symm) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomIso K ((ihom (Δ[1] : SSet.{u})).obj X)
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex).symm

/-- 概要：可逆 path と内部 Hom の比較は、条件を忘れると内部 Hom の交換になる。
方針：二つの全部分複体の比較の包含上の等式を使う。
規約：同型の順方向についての等式。
使われ方：Kerodon §4.5.3（Tag 032Y） の両端の自然性。 -/
lemma equivalencePathInternalHomIso_hom_ι (K X : SSet.{u}) [Quasicategory X] :
    (equivalencePathInternalHomIso K X).hom ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι ((ihom K).obj X) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso Δ[1] K X).hom := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι
  dsimp only [equivalencePathInternalHomIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomIso_inv_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexIso_hom_ι]

/-- 概要：可逆 path と内部 Hom の比較は両端の評価を保つ。
方針：条件を忘れた交換の同型と評価の等式を使う。
規約：両端 i は任意。
使われ方：Kerodon §4.5.5（Tag 01F6） の制限に対する相対 path。 -/
lemma equivalencePathInternalHomIso_endpoint (K X : SSet.{u}) [Quasicategory X] (i : Fin 2) :
    (equivalencePathInternalHomIso K X).hom ≫ (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X i) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((ihom K).obj X) i := by
  change (equivalencePathInternalHomIso K X).hom ≫
    (ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i)) = _
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc,
    equivalencePathInternalHomIso_hom_ι, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_evaluate]
  rfl

/-- 概要：可逆 path と内部 Hom の比較は始域の制限と可換。
方針：全部分複体の包含で比較し、内部 Hom の交換の自然性を使う。
規約：i は任意の射、X は quasicategory。
使われ方：Kerodon §4.5.5（Tag 01F6） の制限の相対 path の持ち上げ。 -/
lemma equivalencePathInternalHomIso_pre {A B X : SSet.{u}} [Quasicategory X] (i : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre i).app X) ≫ (equivalencePathInternalHomIso A X).hom =
      (equivalencePathInternalHomIso B X).hom ≫ (pre i).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X) := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X) := by unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι; infer_instance
  have : Mono ((ihom A).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X)) := (ihom A).map_mono _
  apply (cancel_mono ((ihom A).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X))).1
  have hn := (pre i).naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X)
  calc
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre i).app X) ≫ (equivalencePathInternalHomIso A X).hom) ≫
        (ihom A).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre i).app X) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι ((ihom A).obj X) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso Δ[1] A X).hom) := by
      rw [Category.assoc, equivalencePathInternalHomIso_hom_ι]
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι ((ihom B).obj X) ≫ (ihom (Δ[1] : SSet.{u})).map ((pre i).app X)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso Δ[1] A X).hom := by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_ι]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι ((ihom B).obj X) ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso Δ[1] B X).hom ≫ (pre i).app ((ihom (Δ[1] : SSet.{u})).obj X)) := by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_pre]
    _ = ((equivalencePathInternalHomIso B X).hom ≫ (ihom B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X)) ≫
        (pre i).app ((ihom (Δ[1] : SSet.{u})).obj X) := by
      rw [equivalencePathInternalHomIso_hom_ι, Category.assoc]
    _ = ((equivalencePathInternalHomIso B X).hom ≫ (pre i).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X)) ≫
        (ihom A).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X) := by
      rw [Category.assoc, hn, ← Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
