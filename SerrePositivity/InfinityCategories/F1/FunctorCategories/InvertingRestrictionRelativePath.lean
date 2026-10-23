module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RelativePathSquare
public import SerrePositivity.InfinityCategories.Core.EquivalencePullbackPathLifting

/-!
概要：反転関手の制限の、端点と境界を固定した可逆 path の相対持ち上げ。
方針：周囲の関手空間で持ち上げ、同型不変な頂点条件で全部分複体へ戻す。
規約：持ち上げ済みの部分パラメーターと指定端点を厳密に保つ。
使われ方：局所化同値をセル付加に沿って貼り合わせる相対比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同型不変な全部分複体への制限は、相対可逆 path の全境界持ち上げを保つ。 -/
lemma trivialKanFibration_relativePath_fullRestriction {X Y : SSet.{u}} [Quasicategory X]
    (P : X _⦋0⦌ → Prop) (hP : ∀ {x y}, VertexIso x y → (P x ↔ P y))
    (Q : Y _⦋0⦌ → Prop)
    (p : (fullSubcomplexOnVertices X P : SSet.{u}) ⟶ fullSubcomplexOnVertices Y Q)
    (q : X ⟶ Y)
    (h : p ≫ (fullSubcomplexOnVertices Y Q).ι = (fullSubcomplexOnVertices X P).ι ≫ q)
    (j : Fin 2) [TrivialKanFibration (relativeEquivalencePathMapAt q j)] :
    TrivialKanFibration (relativeEquivalencePathMapAt p j) := by
  let r := relativePathSquareTargetMap p q (fullSubcomplexOnVertices X P).ι
    (fullSubcomplexOnVertices Y Q).ι h j
  constructor
  intro U V i hi
  have : HasLiftingProperty i (relativeEquivalencePathMapAt q j) :=
    TrivialKanFibration.mem (p := relativeEquivalencePathMapAt q j) i hi
  constructor
  intro a b sq
  have hs : CommSq (a ≫ equivalencePathMap (fullSubcomplexOnVertices X P).ι) i
      (relativeEquivalencePathMapAt q j) (b ≫ r) := by
    constructor
    rw [Category.assoc, ← relativePathSquare_comm, ← Category.assoc, sq.w, Category.assoc]
  let F := hs.lift
  have hend : F ≫ equivalencePathEndpoint X j =
      b ≫ pullback.snd (equivalencePathEndpoint
        (fullSubcomplexOnVertices Y Q : SSet.{u}) j) p ≫ (fullSubcomplexOnVertices X P).ι := by
    have he := congrArg
      (fun m : V ⟶ relativeEquivalencePathTargetAt q j ↦
        m ≫ pullback.snd (equivalencePathEndpoint Y j) q) hs.fac_right
    simpa only [r, Category.assoc, relativeEquivalencePathMapAt_snd,
      relativePathSquareTargetMap_snd] using he
  have hj : ∀ v : V _⦋0⦌,
      P ((F ≫ equivalencePathEndpoint X j).app (Opposite.op ⦋0⦌) v) := by
    intro v
    rw [hend]
    exact fullSubcomplexOnVertices_vertex
      ((b ≫ pullback.snd (equivalencePathEndpoint
        (fullSubcomplexOnVertices Y Q : SSet.{u}) j) p).app (Opposite.op ⦋0⦌) v)
  let L := fullSubcomplexEquivalencePathLift P hP F j hj
  have hL : L ≫ equivalencePathMap (fullSubcomplexOnVertices X P).ι = F :=
    fullSubcomplexEquivalencePathLift_map P hP F j hj
  refine CommSq.HasLift.mk' { l := L, fac_left := ?_, fac_right := ?_ }
  · apply (cancel_mono (equivalencePathMap (fullSubcomplexOnVertices X P).ι)).mp
    rw [Category.assoc, hL]
    exact hs.fac_left
  · apply (cancel_mono r).mp
    rw [Category.assoc, relativePathSquare_comm, ← Category.assoc, hL]
    exact hs.fac_right

/-- 単射への反転関手の制限は、可逆 path を両端のいずれを指定しても相対的に持ち上げる。 -/
instance transportSimplexInvertingRestriction_relativePath_trivialKanFibration
    {B D : SSet.{u}} (f : B ⟶ D) [Mono f] (E : SSet.{u}) [Quasicategory E] (j : Fin 2) :
    TrivialKanFibration
      (relativeEquivalencePathMapAt (transportSimplexInvertingRestriction f E) j) := by
  have : TrivialKanFibration
      (relativeEquivalencePathMapAt ((pre (nerveMap (transportSimplexFunctor f))).app E) j) :=
    trivialKanFibration_relativeEquivalencePathMapAt_pre _ E j
  exact trivialKanFibration_relativePath_fullRestriction
    (IsInvertingFunctorVertex _ E (transportSimplexInitialEdges D))
    (fun e ↦ isInvertingFunctorVertex_iff_of_vertexIso _ e)
    (IsInvertingFunctorVertex _ E (transportSimplexInitialEdges B))
    (transportSimplexInvertingRestriction f E) ((pre (nerveMap (transportSimplexFunctor f))).app E)
    (transportSimplexInvertingRestriction_ι f E) j

/-- 単射への反転関手の制限に沿う引き戻しは、quasicategory の同値を保つ。 -/
lemma IsQCatEquivalence.pullback_snd_invertingRestriction {B D E Z : SSet.{u}}
    [Quasicategory E] [Quasicategory Z] (f : B ⟶ D) [Mono f]
    {e : Z ⟶ (invertingFunctors (nerve (TransportSimplexCategory B)) E
      (transportSimplexInitialEdges B) : SSet.{u})} (he : IsQCatEquivalence e) :
    IsQCatEquivalence (pullback.snd e (transportSimplexInvertingRestriction f E)) :=
  he.pullback_snd_of_relativePath _

end SerrePositivity.InfinityCategories
