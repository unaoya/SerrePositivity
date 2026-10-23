module

public import SerrePositivity.InfinityCategories.F2.Presentable.LocalSectionComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeApexEvaluation

/-!
概要：局所対象は元の任意の coherent 図式の極限で閉じる。
方針：切断の底への制限と頂点評価を後合成と照合し、二対三則を使う。
規約：添字は任意の単体集合。反射の存在や presentable 性は仮定しない。
使われ方：HTT 5.5.4 の局所対象の閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 図式の等式による切断の移送は、元の底上の後合成と可換。 -/
lemma relativeFunctorPost_transport {K E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    {a b : K ⟶ B} (h : a = b) :
    relativeFunctorPost p q f hf a ≫ eqToHom (congrArg (relativeFunctorSpace q) h) =
      eqToHom (congrArg (relativeFunctorSpace p) h) ≫ relativeFunctorPost p q f hf b := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 錐の切断の制限は、始点を変える coslice の底上の射と可換。 -/
lemma coneSectionRestriction_post {K X : SSet.{u}} {D : K ⟶ X} (c : JoinCone D)
    (x y : X _⦋0⦌) (f : sliceUnder (SSet.yonedaEquiv.symm y) ⟶
      sliceUnder (SSet.yonedaEquiv.symm x))
    (hf : f ≫ sliceUnderProjection (SSet.yonedaEquiv.symm x) =
      sliceUnderProjection (SSet.yonedaEquiv.symm y)) :
    relativeFunctorPost _ _ f hf c.val ≫ coneSectionRestriction c x =
      coneSectionRestriction c y ≫ relativeFunctorPost _ _ f hf D := by
  unfold coneSectionRestriction
  rw [← Category.assoc, relativeFunctorPost_pre, Category.assoc,
    relativeFunctorPost_transport, ← Category.assoc]
  exact c.property

/-- 錐の頂点評価は、始点を変える coslice の底上の射と可換。 -/
lemma coneApexSectionEvaluation_post {K X : SSet.{u}} {D : K ⟶ X} (c : JoinCone D)
    (x y : X _⦋0⦌) (f : sliceUnder (SSet.yonedaEquiv.symm y) ⟶
      sliceUnder (SSet.yonedaEquiv.symm x))
    (hf : f ≫ sliceUnderProjection (SSet.yonedaEquiv.symm x) =
      sliceUnderProjection (SSet.yonedaEquiv.symm y)) :
    relativeFunctorPost _ _ f hf c.val ≫ coneApexSectionEvaluation c x =
      coneApexSectionEvaluation c y ≫ vertexFiberMap _ _ f hf c.vertex := by
  apply vertexFiber_hom_ext (sliceUnderProjection (SSet.yonedaEquiv.symm x)) c.vertex
  rw [Category.assoc, coneApexSectionEvaluation_ι, ← Category.assoc,
    relativeFunctorPost_ι, Category.assoc, Category.assoc, vertexFiberMap_ι,
    ← Category.assoc]
  conv_rhs => rw [← Category.assoc, coneApexSectionEvaluation_ι]
  rw [Category.assoc]
  rfl

/-- 極限錐の底への切断の前合成が同値なら、元の頂点への前合成も同値。 -/
lemma isLocalForHom_limitCone_of_sections {K X : SSet.{u}} [Quasicategory X]
    {D : K ⟶ X} (c : JoinCone D) (hc : IsLimitCone c)
    (e : (Δ[1] : SSet.{u}) ⟶ X) :
    let x := SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ e)
    let y := SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e)
    let ha : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm x :=
      (Equiv.symm_apply_apply _ _).symm
    let hb : stdSimplex.δ (0 : Fin 2) ≫ e = SSet.yonedaEquiv.symm y :=
      (Equiv.symm_apply_apply _ _).symm
    IsQCatEquivalence (relativeFunctorPost _ _
      (cosliceEdgePrecompositionAt e _ _ ha hb)
      (cosliceEdgePrecompositionAt_projection e _ _ ha hb) D) →
    IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk (edgeCosliceEdge e)) c.vertex := by
  dsimp only
  intro h
  let x := SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ e)
  let y := SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e)
  let ha : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm x :=
    (Equiv.symm_apply_apply _ _).symm
  let hb : stdSimplex.δ (0 : Fin 2) ≫ e = SSet.yonedaEquiv.symm y :=
    (Equiv.symm_apply_apply _ _).symm
  let f := cosliceEdgePrecompositionAt e _ _ ha hb
  have hf := cosliceEdgePrecompositionAt_projection e _ _ ha hb
  have hr := (isLimitCone_iff_coneSectionRestriction_homotopyEquivalence c).mp hc
  have hs : IsQCatEquivalence (relativeFunctorPost _ _ f hf c.val) := by
    apply (hr x).isQCatEquivalence.cancel_right
    rw [coneSectionRestriction_post c x y f hf]
    exact (hr y).isQCatEquivalence.comp h
  have hx := (coneApexSectionEvaluation_homotopyEquivalence c x).isQCatEquivalence
  have hy := (coneApexSectionEvaluation_homotopyEquivalence c y).isQCatEquivalence
  apply (isLocalForHom_edge_iff_coslicePrecomposition e _ _ ha hb c.vertex).mpr
  apply hy.cancel_left
  change IsQCatEquivalence (coneApexSectionEvaluation c y ≫ vertexFiberMap _ _ f hf c.vertex)
  rw [← coneApexSectionEvaluation_post c x y f hf]
  exact hs.comp hx

/-- 局所対象を頂点に持つ任意の coherent 図式の元の極限頂点は局所。 -/
lemma isLocalObject_limitCone {K X : SSet.{u}} [Quasicategory X]
    (W : Set (X _⦋1⦌)) {D : K ⟶ X} (c : JoinCone D) (hc : IsLimitCone c)
    (hD : ∀ k : K _⦋0⦌, IsLocalObject W (D.app (Opposite.op ⦋0⦌) k)) :
    IsLocalObject W c.vertex := by
  intro s hs
  let e := SSet.yonedaEquiv.symm s
  have he : SSet.yonedaEquiv e ∈ W := by simpa only [e, Equiv.apply_symm_apply] using hs
  have hl := isLocalForHom_limitCone_of_sections c hc e
    (localDiagram_coslicePrecomposition_isQCatEquivalence W e he _ _ _ _ D hD)
  have hl' := (isLocalForHom_homMk_iff_edgeOfSimplex (edgeCosliceEdge e) c.vertex).mp hl
  have heq : (edgeCosliceEdge e).edge = s := Equiv.apply_symm_apply SSet.yonedaEquiv s
  rwa [heq] at hl'

end SerrePositivity.InfinityCategories.HomotopyLimits
