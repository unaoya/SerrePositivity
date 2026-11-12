module

public import SerrePositivity.KST.Spectra.D3IteratedLoopDiagramReflection

/-!
概要：元の四次元実端点図式を、二つの順序で反復 loop 図式として保持する。
方針：同じ共同族を curry し、終点射影の自明 Kan 性から外側 loop 性を反映する。
規約：全パラメータ・全 Hom・全単体を保持する。使われ方：二方向比較の幾何的照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

/-- 第一方向を内部 loop 図式とする、同じ四次元図式の外側四角形族。 -/
def d3DoubleEndpointIteratedLeftSquare : PointedKanInfinity.{u} ⟶
    (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity) :=
  curry ((β_ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) PointedKanInfinity).hom ≫
    d3DoubleEndpointJointLeftLoopFamily)

/-- 第二方向を内部 loop 図式とする、元の同じ全単体の外側四角形族。 -/
def d3DoubleEndpointIteratedRightSquare : PointedKanInfinity.{u} ⟶
    (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity) :=
  curry ((β_ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) PointedKanInfinity).hom ≫
    d3DoubleEndpointJointRightLoopFamily)

/-- 内側の角評価は、元の同じ第二方向実面の全四角形に厳密一致する。 -/
lemma d3DoubleEndpointIteratedLeftSquare_inner (i j : Fin 2) :
    d3DoubleEndpointIteratedLeftSquare.{u} ≫
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j) =
    d3DoubleEndpointRightLoopFamily i j ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι := by
  rw [d3DoubleEndpointIteratedLeftSquare, ← curry_natural_right, Category.assoc,
    d3DoubleEndpointJointLeftLoopFamily_corner, ← Category.assoc,
    SymmetricCategory.symmetry, Category.id_comp, curry_uncurry]

/-- 他方の内部角評価も、元の同じ第一方向実面の全四角形を回収する。 -/
lemma d3DoubleEndpointIteratedRightSquare_inner (i j : Fin 2) :
    d3DoubleEndpointIteratedRightSquare.{u} ≫
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity i j) =
    d3DoubleEndpointLeftLoopFamily i j ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι := by
  rw [d3DoubleEndpointIteratedRightSquare, ← curry_natural_right, Category.assoc,
    d3DoubleEndpointJointRightLoopFamily_corner, ← Category.assoc,
    SymmetricCategory.symmetry, Category.id_comp, curry_uncurry]

/-- 内側終点の同じ実面 loop 性を反映し、外側も実 loop 図式と認証する。 -/
lemma d3DoubleEndpointIteratedLeftSquare_isLoop (v : PointedKanInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex (d3DoubleEndpointIteratedLeftSquare.app _ v) := by
  let := d3PointedKanLoopEvaluation_trivial.{u}
  apply (d3IsLoopDiagramVertex_iff_trivialKan_image
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) _).mpr
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex ((d3DoubleEndpointIteratedLeftSquare ≫
    (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)).app _ v)
  rw [d3DoubleEndpointIteratedLeftSquare_inner]
  have h := (d3DoubleEndpointRightLoopFamily 1 1 |>.app _ v).property (𝟙 ⦋0⦌)
  simpa only [op_id, CategoryTheory.Functor.map_id_apply, NatTrans.comp_app,
    Subfunctor.ι, types_comp_apply, TypeCat.ofHom_apply] using h

/-- 逆順の同じ四次元図式も、同じ終点射影の下で反復 loop 図式となる。 -/
lemma d3DoubleEndpointIteratedRightSquare_isLoop (v : PointedKanInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex (d3DoubleEndpointIteratedRightSquare.app _ v) := by
  let := d3PointedKanLoopEvaluation_trivial.{u}
  apply (d3IsLoopDiagramVertex_iff_trivialKan_image
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) _).mpr
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex ((d3DoubleEndpointIteratedRightSquare ≫
    (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)).app _ v)
  rw [d3DoubleEndpointIteratedRightSquare_inner]
  have h := (d3DoubleEndpointLeftLoopFamily 1 1 |>.app _ v).property (𝟙 ⦋0⦌)
  simpa only [op_id, CategoryTheory.Functor.map_id_apply, NatTrans.comp_app,
    Subfunctor.ι, types_comp_apply, TypeCat.ofHom_apply] using h

/-- 第一方向を内側に持つ、元の同じ反復 loop 全図式族。 -/
def d3DoubleEndpointIteratedLeftFamily : PointedKanInfinity.{u} ⟶
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex d3DoubleEndpointIteratedLeftSquare
    d3DoubleEndpointIteratedLeftSquare_isLoop

/-- 第二方向を内側に持つ、元の同じ反復 loop 全図式族。 -/
def d3DoubleEndpointIteratedRightFamily : PointedKanInfinity.{u} ⟶
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex d3DoubleEndpointIteratedRightSquare
    d3DoubleEndpointIteratedRightSquare_isLoop

/-- 外側の角を固定すると、元の同じ左実面族を全 Hom・全単体で回収する。 -/
lemma d3DoubleEndpointIteratedLeftFamily_corner (k l : Fin 2) :
    d3DoubleEndpointIteratedLeftFamily.{u} ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity) k l =
    d3DoubleEndpointLeftLoopFamily k l := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation]
  rw [← Category.assoc, d3DoubleEndpointIteratedLeftFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι,
    d3DoubleEndpointIteratedLeftSquare, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  have hb : lift
      (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l))
      (𝟙 PointedKanInfinity.{u}) ≫
        (β_ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) PointedKanInfinity).hom =
    lift (𝟙 PointedKanInfinity)
      (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)) := rfl
  rw [← Category.assoc, hb, d3DoubleEndpointJointLeftLoopFamily_face]

/-- 逆順でも、元の同じ右実面族を全 Hom・全単体で回収する。 -/
lemma d3DoubleEndpointIteratedRightFamily_corner (k l : Fin 2) :
    d3DoubleEndpointIteratedRightFamily.{u} ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity) k l =
    d3DoubleEndpointRightLoopFamily k l := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation]
  rw [← Category.assoc, d3DoubleEndpointIteratedRightFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι,
    d3DoubleEndpointIteratedRightSquare, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  have hb : lift
      (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l))
      (𝟙 PointedKanInfinity.{u}) ≫
        (β_ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) PointedKanInfinity).hom =
    lift (𝟙 PointedKanInfinity)
      (SSet.const (stdSimplex.obj₀Equiv.symm k, stdSimplex.obj₀Equiv.symm l)) := rfl
  rw [← Category.assoc, hb, d3DoubleEndpointJointRightLoopFamily_face]

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
