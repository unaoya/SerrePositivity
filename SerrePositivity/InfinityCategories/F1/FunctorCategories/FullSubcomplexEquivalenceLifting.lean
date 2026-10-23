module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullSubcomplexPathLift
public import SerrePositivity.InfinityCategories.F1B.KanEquivalenceLifting

/-!
概要：同型不変な全部分複体への所属と、単射な前合成同値の右持ち上げ。
方針：前合成の同値と充満忠実性で所属条件を全頂点へ戻す。
規約：条件を未証明の instance として仮定せず、反転関手の制限で実際に証明する。
使われ方：比較四角形の終点側の持ち上げを可逆比較へ強める。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同型不変な全部分複体への所属条件は、前合成同値から全頂点へ回収できる。 -/
lemma fullSubcomplex_condition_of_precompositionEquivalence {A B X : SSet.{u}}
    [Quasicategory X] (P : X _⦋0⦌ → Prop)
    (hP : ∀ {x y}, VertexIso x y → (P x ↔ P y)) (i : A ⟶ B)
    (hi : IsPrecompositionEquivalence i) (a : A ⟶ (fullSubcomplexOnVertices X P : SSet.{u}))
    (f : B ⟶ X) (ha : a ≫ (fullSubcomplexOnVertices X P).ι = i ≫ f) :
    ∀ b : B _⦋0⦌, P (f.app (Opposite.op ⦋0⦌) b) := by
  have he := (hi (fullSubcomplexOnVertices X P : SSet.{u})).choose.isEssentiallySurjective
  obtain ⟨g₀, ⟨eg⟩⟩ := he (functorVertex a)
  obtain ⟨g, rfl⟩ := (functorVertexEquiv B
    (fullSubcomplexOnVertices X P : SSet.{u})).surjective g₀
  change FunctorIso (i ≫ g) a at eg
  have ep : FunctorIso (i ≫ (g ≫ (fullSubcomplexOnVertices X P).ι)) (i ≫ f) := by
    simpa only [Category.assoc, ha] using
      (FunctorIso.postcomp eg (fullSubcomplexOnVertices X P).ι)
  let hf := (hi X).isFullyFaithful.toHoFullyFaithful
  let e : FunctorIso (g ≫ (fullSubcomplexOnVertices X P).ι) f :=
    hf.preimageIso
      (X := HomotopyCategory.mk (functorVertex (g ≫ (fullSubcomplexOnVertices X P).ι)))
      (Y := HomotopyCategory.mk (functorVertex f)) ep
  intro b
  have eb : VertexIso ((g ≫ (fullSubcomplexOnVertices X P).ι).app (Opposite.op ⦋0⦌) b)
      (f.app (Opposite.op ⦋0⦌) b) := e.toNatIso.app (HomotopyCategory.mk b)
  exact (hP eb).mp (fullSubcomplexOnVertices_vertex (g.app (Opposite.op ⦋0⦌) b))

/-- 同型不変な全部分複体の包含は、単射な前合成同値を右に持ち上げる。 -/
lemma kanEquivalenceLifting_fullSubcomplexOnVertices_ι {X : SSet.{u}} [Quasicategory X]
    (P : X _⦋0⦌ → Prop) (hP : ∀ {x y}, VertexIso x y → (P x ↔ P y)) :
    F1B.KanEquivalenceLifting (fullSubcomplexOnVertices X P).ι := by
  intro A B i _ hi
  constructor
  intro a b sq
  let L := fullSubcomplexLift P b
    (fullSubcomplex_condition_of_precompositionEquivalence P hP i hi a b sq.w)
  have hL : L ≫ (fullSubcomplexOnVertices X P).ι = b := fullSubcomplexLift_ι _ _ _
  refine CommSq.HasLift.mk' { l := L, fac_left := ?_, fac_right := hL }
  apply (cancel_mono (fullSubcomplexOnVertices X P).ι).mp
  rw [Category.assoc, hL]
  exact sq.w.symm

/-- 頂点を全て被覆する射は、任意の全部分複体の包含に対して持ち上がる。 -/
lemma hasLiftingProperty_fullSubcomplexOnVertices_ι_of_vertex_surjective
    {A B X : SSet.{u}} (P : X _⦋0⦌ → Prop) (i : A ⟶ B)
    (hi : Function.Surjective (i.app (Opposite.op ⦋0⦌))) :
    HasLiftingProperty i (fullSubcomplexOnVertices X P).ι := by
  constructor
  intro a b sq
  have hv (v : B _⦋0⦌) : P (b.app (Opposite.op ⦋0⦌) v) := by
    obtain ⟨w, rfl⟩ := hi v
    have hw := fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) w)
    have he := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) w) sq.w
    exact he ▸ hw
  let L := fullSubcomplexLift P b hv
  have hL : L ≫ (fullSubcomplexOnVertices X P).ι = b := fullSubcomplexLift_ι _ _ _
  refine CommSq.HasLift.mk' { l := L, fac_left := ?_, fac_right := hL }
  apply (cancel_mono (fullSubcomplexOnVertices X P).ι).mp
  rw [Category.assoc, hL]
  exact sq.w.symm

/-- 全部分複体間の制限は、周囲の射の前合成同値の持ち上げを受け継ぐ。 -/
lemma kanEquivalenceLifting_fullRestriction {X Y : SSet.{u}} [Quasicategory X]
    (P : X _⦋0⦌ → Prop) (hP : ∀ {x y}, VertexIso x y → (P x ↔ P y))
    (Q : Y _⦋0⦌ → Prop)
    (p : (fullSubcomplexOnVertices X P : SSet.{u}) ⟶ fullSubcomplexOnVertices Y Q)
    (q : X ⟶ Y)
    (h : p ≫ (fullSubcomplexOnVertices Y Q).ι = (fullSubcomplexOnVertices X P).ι ≫ q)
    (hq : F1B.KanEquivalenceLifting q) : F1B.KanEquivalenceLifting p := by
  intro A B i hi hiE
  constructor
  intro a b sq
  have hs : CommSq (a ≫ (fullSubcomplexOnVertices X P).ι) i q
      (b ≫ (fullSubcomplexOnVertices Y Q).ι) := by
    constructor
    rw [Category.assoc, ← h, ← Category.assoc, sq.w, Category.assoc]
  have := hq i hi hiE
  let L := fullSubcomplexLift P hs.lift
    (fullSubcomplex_condition_of_precompositionEquivalence P hP i hiE a hs.lift
      hs.fac_left.symm)
  have hL : L ≫ (fullSubcomplexOnVertices X P).ι = hs.lift :=
    fullSubcomplexLift_ι _ _ _
  refine CommSq.HasLift.mk' { l := L, fac_left := ?_, fac_right := ?_ }
  · apply (cancel_mono (fullSubcomplexOnVertices X P).ι).mp
    rw [Category.assoc, hL, hs.fac_left]
  · apply (cancel_mono (fullSubcomplexOnVertices Y Q).ι).mp
    rw [Category.assoc, h, ← Category.assoc, hL, hs.fac_right]

/-- 可逆な区間関手を表す頂点条件は、関手同型で不変。 -/
lemma isEquivalencePathVertex_iff_of_vertexIso {X : SSet.{u}}
    {a b : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌} (e : VertexIso a b) :
    IsEquivalencePathVertex a ↔ IsEquivalencePathVertex b := by
  obtain ⟨F, rfl⟩ := (functorVertexEquiv Δ[1] X).surjective a
  obtain ⟨G, rfl⟩ := (functorVertexEquiv Δ[1] X).surjective b
  have he := Set.ext_iff.mp (invertedEdges_functorIso e)
    (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
  change IsEquivalencePathVertex (functorVertex F) ↔ IsEquivalencePathVertex (functorVertex G)
  change IsInvertibleEdge (edgeOfSimplex (intervalFunctorVertexEdge (functorVertex F))) ↔
    IsInvertibleEdge (edgeOfSimplex (intervalFunctorVertexEdge (functorVertex G)))
  rw [intervalFunctorVertexEdge_functorVertex, intervalFunctorVertexEdge_functorVertex]
  have hf (f : (Δ[1] : SSet.{u}) ⟶ X) :
      IsInvertibleEdge ((edgeOfSimplex (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))).map
        ((truncation 2).map f)) ↔ IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv f)) := by
    apply isInvertibleEdge_congr
    change f.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
      SSet.yonedaEquiv f
    rw [← SSet.yonedaEquiv_comp, Category.id_comp]
  exact (hf F).symm.trans (he.trans (hf G))

/-- 可逆 path の包含は、単射な前合成同値を右に持ち上げる。 -/
lemma kanEquivalenceLifting_equivalencePathι (X : SSet.{u}) [Quasicategory X] :
    F1B.KanEquivalenceLifting (equivalencePathι X) :=
  kanEquivalenceLifting_fullSubcomplexOnVertices_ι IsEquivalencePathVertex
    (fun e ↦ isEquivalencePathVertex_iff_of_vertexIso e)

/-- 単射への反転関手の制限は、前合成同値を指定部分ごと厳密に持ち上げる。 -/
lemma kanEquivalenceLifting_transportSimplexInvertingRestriction {B D : SSet.{u}}
    (f : B ⟶ D) [Mono f] (E : SSet.{u}) [Quasicategory E] :
    F1B.KanEquivalenceLifting (transportSimplexInvertingRestriction f E) := by
  exact kanEquivalenceLifting_fullRestriction
    (IsInvertingFunctorVertex _ E (transportSimplexInitialEdges D))
    (fun e ↦ isInvertingFunctorVertex_iff_of_vertexIso _ e)
    (IsInvertingFunctorVertex _ E (transportSimplexInitialEdges B))
    (transportSimplexInvertingRestriction f E)
    ((pre (nerveMap (transportSimplexFunctor f))).app E)
    (transportSimplexInvertingRestriction_ι f E)
    (F1B.kanEquivalenceLifting_pre (nerveMap (transportSimplexFunctor f)))

end SerrePositivity.InfinityCategories
