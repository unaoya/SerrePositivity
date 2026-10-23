module

public import SerrePositivity.InfinityCategories.F1.LeftPath
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BoundaryPrism

/-!
概要：cocartesian な辺の関手単体集合と相対始点評価。
方針：区間からの関手の cocartesian な頂点が張る全部分複体を取る。
規約：底の辺も保持し、始点だけを自由な底としない。
使われ方：Kerodon Lemma 5.2.2.13、covariant transport の整合的な選択。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：cocartesian な辺を表す関手頂点の条件。
方針：区間からの射が表す一単体の cocartesian 性を課す。
規約：p の fibration 性は不要。
使われ方：Kerodon Lemma 5.2.2.13、cocartesian な prism の頂点条件。 -/
def IsCocartesianPathVertex {X B : SSet.{u}} (p : X ⟶ B)
    (v : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌) : Prop :=
  IsCocartesianEdge p (intervalFunctorVertexEdge v)

/-- 概要：cocartesian な辺が張る関手単体集合の全部分複体。
方針：全ての頂点に cocartesian 性を要求する。
規約：辺の両端は固定しない。
使われ方：Kerodon Lemma 5.2.2.13、transport の相対的な辺の空間。 -/
def cocartesianPath {X B : SSet.{u}} (p : X ⟶ B) : SSet.{u} :=
  (fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj X)
    (IsCocartesianPathVertex p) : SSet.{u})

/-- 概要：cocartesian path を区間からの関手単体集合に含める。
方針：全部分複体の包含を使う。
規約：全次数で単射。
使われ方：Kerodon Lemma 5.2.2.13、prism への uncurry。 -/
def cocartesianPathι {X B : SSet.{u}} (p : X ⟶ B) :
    cocartesianPath p ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  (fullSubcomplexOnVertices _ (IsCocartesianPathVertex p)).ι

/-- 概要：cocartesian path から始点と底の辺の族を取る。
方針：包含の後で相対始点評価を適用する。
規約：標的は relativeEdgeSourceTarget p。
使われ方：Kerodon Lemma 5.2.2.13、transport の存在と一意性。 -/
noncomputable def cocartesianPathSource {X B : SSet.{u}} (p : X ⟶ B) :
    cocartesianPath p ⟶ relativeEdgeSourceTarget p :=
  cocartesianPathι p ≫ relativeEdgeSource p

/-- 概要：cocartesian な区間からの射を path の頂点として表す。
方針：零単体から自身への全ての射が恒等射であることを使う。
規約：元の区間からの射 f を保つ。
使われ方：Kerodon Lemma 5.2.2.13、零次元の境界の持ち上げ。 -/
def cocartesianPathVertex {X B : SSet.{u}} (p : X ⟶ B) (f : (Δ[1] : SSet.{u}) ⟶ X)
    (hf : IsCocartesianEdge p (SSet.yonedaEquiv f)) : (cocartesianPath p) _⦋0⦌ :=
  ⟨functorVertex f, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    subst α
    simp only [op_id, CategoryTheory.Functor.map_id_apply]
    change IsCocartesianEdge p (intervalFunctorVertexEdge (functorVertex f))
    rwa [intervalFunctorVertexEdge_functorVertex]⟩

/-- 概要：cocartesian fibration の相対始点評価は零次元の図式を持ち上げる。
方針：底の辺と始点を引き戻しから読み、定義の cocartesian lift を取る。
規約：底や全空間の quasicategory 性は不要。
使われ方：Kerodon Lemma 5.2.2.13、相対評価の零次元境界の充填。 -/
lemma cocartesianPathSource_lift_vertex {X B : SSet.{u}} (p : X ⟶ B)
    [CocartesianFibration p] (b : (Δ[0] : SSet.{u}) ⟶ relativeEdgeSourceTarget p) :
    ∃ g : (Δ[0] : SSet.{u}) ⟶ cocartesianPath p, g ≫ cocartesianPathSource p = b := by
  let ev := evaluateFunctorAt (Y := B) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  let r := pullback.fst p ev
  let s := pullback.snd p ev
  let x := SSet.yonedaEquiv (b ≫ r)
  let u := (functorVertexEquiv (Δ[1] : SSet.{u}) B).symm (SSet.yonedaEquiv (b ≫ s))
  have hu : functorVertex u = SSet.yonedaEquiv (b ≫ s) :=
    (functorVertexEquiv _ _).apply_symm_apply _
  have hxu : p.app (Opposite.op ⦋0⦌) x = ev.app (Opposite.op ⦋0⦌) (functorVertex u) := by
    rw [hu]
    dsimp only [x]
    rw [← SSet.yonedaEquiv_comp, ← SSet.yonedaEquiv_comp]
    simp only [r, s, Category.assoc, pullback.condition]
  have he : stdSimplex.δ 1 ≫ u =
      SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) x) := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.δ_one_eq_const, SSet.yonedaEquiv_comp, SSet.yonedaEquiv_const,
      Equiv.apply_symm_apply]
    rw [← evaluateFunctorAt_functorVertex]
    exact hxu.symm
  obtain ⟨f, hf, hfp, hfc⟩ := CocartesianFibration.mem (p := p) |>.2 x u he
  let g := SSet.yonedaEquiv.symm (cocartesianPathVertex p f hfc)
  have hg : g ≫ cocartesianPathι p = SSet.yonedaEquiv.symm (functorVertex f) := by
    rw [SSet.yonedaEquiv_symm_comp]
    rfl
  have hf' : SSet.yonedaEquiv.symm (functorVertex f) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = SSet.yonedaEquiv.symm x := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, evaluateFunctorAt_functorVertex,
      Equiv.apply_symm_apply]
    have h := congrArg SSet.yonedaEquiv hf
    simpa only [stdSimplex.δ_one_eq_const, SSet.yonedaEquiv_comp, SSet.yonedaEquiv_const,
      Equiv.apply_symm_apply] using h
  refine ⟨g, ?_⟩
  apply pullback.hom_ext
  · change (g ≫ cocartesianPathSource p) ≫ r = b ≫ r
    simp only [cocartesianPathSource, relativeEdgeSource, r, ev, Category.assoc,
      pullback.lift_fst]
    rw [← Category.assoc, hg, hf']
    exact SSet.yonedaEquiv.symm_apply_apply _
  · change (g ≫ cocartesianPathSource p) ≫ s = b ≫ s
    simp only [cocartesianPathSource, relativeEdgeSource, s, ev, Category.assoc,
      pullback.lift_snd]
    rw [← Category.assoc, hg]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change functorVertex (f ≫ p) = _
    rw [hfp, hu]

end SerrePositivity.InfinityCategories
