module

public import SerrePositivity.KST.Spectra.FibrationCompositionTriangleLift
public import SerrePositivity.KST.Spectra.PointedVerticalChainCompression

/-!
概要：同じ射影を固定する二つの区間を、同じ厳密 Hom fiber 内の実三角形つきで合成する。
方針：後合成 fibration に一定三角形を持ち上げ、対角区間と三角形全体の定数射影を保持する。
規約：全空間や底の Kan 性は不要。使われ方：区間と三角形を保持する相対列厳密化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 同じ射を端点に持ち、同じ射影を固定する定数区間。 -/
def VerticalPath.refl {T E B : PointedSimplicialSet.{u}} (p : E ⟶ B) (f : T ⟶ E) :
    VerticalPath p f f where
  path := SSet.const (familyVertex f)
  zero := by rw [SSet.comp_const, pointFamily_eq_const]
  one := by rw [SSet.comp_const, pointFamily_eq_const]
  «over» := by rw [SSet.const_comp, familyVertex_post]

/-- 対角区間と、同じ射影を全二次元で固定する実際の合成三角形。 -/
structure VerticalPathComposite {T E B : PointedSimplicialSet.{u}} {p : E ⟶ B}
    {f g h : T ⟶ E} (P : VerticalPath p f g) (Q : VerticalPath p g h) where
  path : VerticalPath p f h
  triangle : SSet.Edge.CompStruct P.edge Q.edge path.edge
  triangle_over : SSet.yonedaEquiv.symm triangle.simplex ≫
    (PointedObject.basedHomMap T p).right = SSet.const (familyVertex (f ≫ p))

/-- 同じ Hom fiber の一定三角形へ二辺固定で持ち上げ、垂直合成区間を構成する。 -/
def VerticalPathComposite.choose {T E B : PointedSimplicialSet.{u}} {p : E ⟶ B}
    (hp : SSet.modelCategoryQuillen.J.rlp p.right) {f g h : T ⟶ E}
    (P : VerticalPath p f g) (Q : VerticalPath p g h) : VerticalPathComposite P Q := by
  let pFibration : Fibration p.right := (SSet.modelCategoryQuillen.fibration_iff _).2 hp
  let postFibration : Fibration (PointedObject.basedHomMap T p).right := post_fibration T p
  have hpost : SSet.modelCategoryQuillen.J.rlp (PointedObject.basedHomMap T p).right :=
    (SSet.modelCategoryQuillen.fibration_iff _).1 inferInstance
  let φ : SSet.stdSimplex.obj ⦋2⦌ ⟶ (PointedObject.basedHom T B).right :=
    SSet.const (familyVertex (f ≫ p))
  have hP : SSet.yonedaEquiv.symm P.edge.edge ≫ (PointedObject.basedHomMap T p).right =
      stdSimplex.δ (2 : Fin 3) ≫ φ := by
    change SSet.yonedaEquiv.symm (SSet.yonedaEquiv P.path) ≫ _ = _
    rw [Equiv.symm_apply_apply, P.over, SSet.comp_const]
  have hQ : SSet.yonedaEquiv.symm Q.edge.edge ≫ (PointedObject.basedHomMap T p).right =
      stdSimplex.δ (0 : Fin 3) ≫ φ := by
    change SSet.yonedaEquiv.symm (SSet.yonedaEquiv Q.path) ≫ _ = _
    rw [Equiv.symm_apply_apply, Q.over, P.endpoint_over, SSet.comp_const]
  let hex := exists_composition_triangle_lift (PointedObject.basedHomMap T p).right hpost
    P.edge Q.edge φ hP hQ
  let e := hex.choose
  let t := hex.choose_spec.choose
  have ht := hex.choose_spec.choose_spec
  have he : SSet.yonedaEquiv.symm e.edge ≫ (PointedObject.basedHomMap T p).right =
      SSet.const (familyVertex (f ≫ p)) := by
    have h := congrArg (stdSimplex.δ (1 : Fin 3) ≫ ·) ht
    rw [← Category.assoc, SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm, SSet.comp_const] at h
    exact h
  let R : VerticalPath p f h := {
    path := SSet.yonedaEquiv.symm e.edge
    zero := by
      rw [SSet.Edge.δ_one_yonedaEquiv_symm]
      exact SSet.yonedaEquiv.symm_apply_apply (pointFamily f)
    one := by
      rw [SSet.Edge.δ_zero_yonedaEquiv_symm]
      exact SSet.yonedaEquiv.symm_apply_apply (pointFamily h)
    «over» := he }
  have he' : e.edge = R.edge.edge := by
    change e.edge = SSet.yonedaEquiv (SSet.yonedaEquiv.symm e.edge)
    exact (Equiv.apply_symm_apply _ _).symm
  exact ⟨R, { simplex := t.simplex, d₂ := t.d₂, d₀ := t.d₀, d₁ := t.d₁.trans he' }, ht⟩

/-- 合成三角形全体は、同じ厳密 Hom fiber の実際の二単体へ持ち上がる。 -/
def VerticalPathComposite.fiberTriangle {T E B : PointedSimplicialSet.{u}} {p : E ⟶ B}
    {f g h : T ⟶ E} {P : VerticalPath p f g} {Q : VerticalPath p g h}
    (C : VerticalPathComposite P Q) : (Δ[2] : SSet.{u}) ⟶ verticalFiber p f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift (PointedObject.basedHomMap T p).right (familyVertex (f ≫ p))
    (SSet.yonedaEquiv.symm C.triangle.simplex) C.triangle_over

end SerrePositivity.KST.Spectra.PointedMapping
