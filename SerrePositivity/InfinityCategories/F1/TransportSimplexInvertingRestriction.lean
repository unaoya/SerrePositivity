module

public import SerrePositivity.InfinityCategories.F1.TransportSimplexSubcomplex

/-!
概要：単体圏上の反転関手の、底の射に沿う厳密な制限。
方針：始点を保つ条件の不変性で全部分複体への前合成を定める。
規約：底の充填性は仮定しない。
使われ方：局所化の普遍性を単体作用素・部分複体と両立させる比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 底の射による単体圏の関手は、始点を保つ条件を保ち反映する。 -/
lemma transportSimplexFunctor_preservesFirst_iff {B D : SSet.{u}} (f : B ⟶ D)
    {i j : TransportSimplexCategory B} (g : i ⟶ j) :
    TransportSimplexPreservesFirst ((transportSimplexFunctor f).map g) ↔
      TransportSimplexPreservesFirst g := by
  rw [transportSimplexPreservesFirst_iff, transportSimplexPreservesFirst_iff]
  rfl

/-- 指定した辺の集合は、底の任意の射による添字変換で保たれる。 -/
lemma transportSimplexInitialEdges_map {B D : SSet.{u}} (f : B ⟶ D) :
    (nerveMap (transportSimplexFunctor f)).app (Opposite.op ⦋1⦌) ''
      transportSimplexInitialEdges B ⊆ transportSimplexInitialEdges D := by
  rintro _ ⟨_, ⟨i, j, g, hg, rfl⟩, rfl⟩
  refine ⟨_, _, (transportSimplexFunctor f).map g,
    (transportSimplexFunctor_preservesFirst_iff f g).mpr hg, ?_⟩
  exact (nerveMap_app_mk₁ (transportSimplexFunctor f) g).symm

/-- 指定辺を反転する関手の、底の射に沿う制限も指定辺を反転する。 -/
lemma transportSimplexInvertsEdges_restrict {B D E : SSet.{u}} (f : B ⟶ D)
    (U : nerve (TransportSimplexCategory D) ⟶ E)
    (hU : InvertsEdges U (transportSimplexInitialEdges D)) :
    InvertsEdges (nerveMap (transportSimplexFunctor f) ≫ U)
      (transportSimplexInitialEdges B) := by
  intro s hs
  have h := hU (transportSimplexInitialEdges_map f ⟨s, hs, rfl⟩)
  exact (isInvertibleEdge_congr (e := (edgeOfSimplex s).map
    ((truncation 2).map (nerveMap (transportSimplexFunctor f) ≫ U)))
    (f := (edgeOfSimplex
      ((nerveMap (transportSimplexFunctor f)).app (Opposite.op ⦋1⦌) s)).map
        ((truncation 2).map U)) rfl).mpr h

/-- 反転関手の圏全体の、底の任意の射に沿う前合成。 -/
def transportSimplexInvertingRestriction {B D : SSet.{u}} (f : B ⟶ D) (E : SSet.{u}) :
    (invertingFunctors (nerve (TransportSimplexCategory D)) E
      (transportSimplexInitialEdges D) : SSet.{u}) ⟶
    (invertingFunctors (nerve (TransportSimplexCategory B)) E
      (transportSimplexInitialEdges B) : SSet.{u}) :=
  fullSubcomplexLift
    (IsInvertingFunctorVertex _ E (transportSimplexInitialEdges B))
    ((invertingFunctors (nerve (TransportSimplexCategory D)) E
      (transportSimplexInitialEdges D)).ι ≫
        (pre (nerveMap (transportSimplexFunctor f))).app E) (by
    intro v
    obtain ⟨U, hU⟩ := (functorVertexEquiv _ E).surjective v.val
    have hv := fullSubcomplexOnVertices_vertex v
    change IsInvertingFunctorVertex _ E (transportSimplexInitialEdges D) v.val at hv
    unfold IsInvertingFunctorVertex at hv ⊢
    change InvertsEdges ((functorVertexEquiv _ E).symm
      (((pre (nerveMap (transportSimplexFunctor f))).app E).app (Opposite.op ⦋0⦌) v.val)) _
    rw [← hU] at hv ⊢
    rw [Equiv.symm_apply_apply] at hv
    change InvertsEdges ((functorVertexEquiv _ E).symm
      ((functorVertexEquiv _ E) (nerveMap (transportSimplexFunctor f) ≫ U))) _
    rw [Equiv.symm_apply_apply]
    exact transportSimplexInvertsEdges_restrict f U hv)

/-- 全反転関手の制限を含めると、元の前合成に厳密に一致する。 -/
lemma transportSimplexInvertingRestriction_ι {B D : SSet.{u}} (f : B ⟶ D)
    (E : SSet.{u}) :
    transportSimplexInvertingRestriction f E ≫
        (invertingFunctors (nerve (TransportSimplexCategory B)) E
          (transportSimplexInitialEdges B)).ι =
      (invertingFunctors (nerve (TransportSimplexCategory D)) E
        (transportSimplexInitialEdges D)).ι ≫
          (pre (nerveMap (transportSimplexFunctor f))).app E :=
  fullSubcomplexLift_ι _ _ _

/-- 局所化の前合成比較は、底の全ての射に沿う制限と厳密に可換。 -/
lemma transportSimplexLocalizationPrecomposition_naturality {B D : SSet.{u}}
    (f : B ⟶ D) (E : SSet.{u}) :
    (pre f).app E ≫ localizationPrecomposition (transportSimplexFirstVertexMap B)
        (transportSimplexInitialEdges B) (transportSimplexFirstVertexMap_inverts B) E =
      localizationPrecomposition (transportSimplexFirstVertexMap D)
        (transportSimplexInitialEdges D) (transportSimplexFirstVertexMap_inverts D) E ≫
          transportSimplexInvertingRestriction f E := by
  apply (cancel_mono (invertingFunctors (nerve (TransportSimplexCategory B)) E
    (transportSimplexInitialEdges B)).ι).mp
  rw [Category.assoc, localizationPrecomposition_ι, Category.assoc,
    transportSimplexInvertingRestriction_ι, ← Category.assoc, localizationPrecomposition_ι,
    ← NatTrans.comp_app, ← pre_map, ← NatTrans.comp_app, ← pre_map,
    transportSimplexFirstVertexMap_naturality]

/-- 単体圏への恒等の底変換は恒等関手。 -/
lemma transportSimplexFunctor_id (B : SSet.{u}) :
    transportSimplexFunctor (𝟙 B) = 𝟭 _ := rfl

/-- 単体圏への底変換は合成を厳密に保つ。 -/
lemma transportSimplexFunctor_comp {A B D : SSet.{u}} (f : A ⟶ B) (g : B ⟶ D) :
    transportSimplexFunctor (f ≫ g) = transportSimplexFunctor f ⋙ transportSimplexFunctor g :=
  rfl

/-- 反転関手の恒等の底変換は恒等射。 -/
lemma transportSimplexInvertingRestriction_id (B E : SSet.{u}) :
    transportSimplexInvertingRestriction (𝟙 B) E = 𝟙 _ := by
  apply (cancel_mono (invertingFunctors (nerve (TransportSimplexCategory B)) E
    (transportSimplexInitialEdges B)).ι).mp
  rw [transportSimplexInvertingRestriction_ι, transportSimplexFunctor_id]
  change _ ≫ (pre (𝟙 _)).app E = 𝟙 _ ≫ _
  rw [pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp]

/-- 反転関手の底変換は、順序を逆にして合成を厳密に保つ。 -/
lemma transportSimplexInvertingRestriction_comp {A B D : SSet.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (E : SSet.{u}) :
    transportSimplexInvertingRestriction (f ≫ g) E =
      transportSimplexInvertingRestriction g E ≫ transportSimplexInvertingRestriction f E := by
  apply (cancel_mono (invertingFunctors (nerve (TransportSimplexCategory A)) E
    (transportSimplexInitialEdges A)).ι).mp
  rw [transportSimplexInvertingRestriction_ι, Category.assoc,
    transportSimplexInvertingRestriction_ι, ← Category.assoc,
    transportSimplexInvertingRestriction_ι, Category.assoc]
  change _ ≫ (pre (nerveMap (transportSimplexFunctor f) ≫
    nerveMap (transportSimplexFunctor g))).app E = _
  rw [pre_map, NatTrans.comp_app]

/-- 底を同時に動かした反転関手の厳密な反変図式。 -/
def transportSimplexInvertingDiagram (E : SSet.{u}) : SSet.{u}ᵒᵖ ⥤ SSet.{u} where
  obj B := invertingFunctors (nerve (TransportSimplexCategory B.unop)) E
    (transportSimplexInitialEdges B.unop)
  map f := transportSimplexInvertingRestriction f.unop E
  map_id B := transportSimplexInvertingRestriction_id B.unop E
  map_comp f g := transportSimplexInvertingRestriction_comp g.unop f.unop E

/-- 底上の全関手の、全ての底に関する厳密な反変図式。 -/
def transportBaseRestrictionDiagram (E : SSet.{u}) : SSet.{u}ᵒᵖ ⥤ SSet.{u} where
  obj B := (ihom B.unop).obj E
  map f := (pre f.unop).app E
  map_id B := by
    change (pre (𝟙 B.unop)).app E = _
    rw [pre_id, NatTrans.id_app]
  map_comp f g := by
    change (pre (g.unop ≫ f.unop)).app E = _
    rw [pre_map, NatTrans.comp_app]

/-- 初頂点写像による比較を、全ての底・面・退化を動かす自然変換へ束ねる。 -/
def transportSimplexLocalizationComparison (E : SSet.{u}) :
    transportBaseRestrictionDiagram E ⟶ transportSimplexInvertingDiagram E where
  app B := localizationPrecomposition (transportSimplexFirstVertexMap B.unop)
    (transportSimplexInitialEdges B.unop) (transportSimplexFirstVertexMap_inverts B.unop) E
  naturality {_B _D} f := transportSimplexLocalizationPrecomposition_naturality f.unop E

end SerrePositivity.InfinityCategories
