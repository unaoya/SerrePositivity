module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberEndpointPrecomp
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberEndpointValue
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：指定 fiber 終点比較の係数前合成が、同じ全延長の指定比較と値まで一致する。
方針：元の可縮延長空間の同型を、同じ fiber 評価の前合成で写す。
規約：元の二延長と全初期値を保持。使われ方：指定一点比較を全係数へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定 fiber 比較を前合成しても、同じ二全延長を新しい終点で比較する指定値になる。 -/
lemma relativeExtensionFiberEndpoint_witnessIso_precomp {A D C C' E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B) (i : D ⟶ A)
    (hi : leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ a = SSet.const b)
    (W W' : A ⟶ E) (hW : W ≫ p = a) (hW' : W' ≫ p = a)
    (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
    (g g' : C ⟶ vertexFiber p b)
    (hWj : j ≫ W = g ≫ vertexFiberι p b) (hWj' : j ≫ W' = g' ≫ vertexFiberι p b)
    (s : C' ⟶ C) :
    (relativeExtensionFiberEndpoint_witnessIso p a i hi v hv j b hj
      W W' hW hW' hWi hWi' g g' hWj hWj').precomp s =
    relativeExtensionFiberEndpoint_witnessIso p a i hi v hv (s ≫ j) b
      (by rw [Category.assoc, hj, SSet.comp_const]) W W' hW hW' hWi hWi' (s ≫ g) (s ≫ g')
      (by rw [Category.assoc, hWj, Category.assoc])
      (by rw [Category.assoc, hWj', Category.assoc]) := by
  let e := (relativeFunctorExtensionSpace_isContractibleKan p a i hi v hv).vertexIso
    (relativeFunctorExtensionSpaceVertexEquiv p a i v hv ⟨W, hW, hWi⟩)
    (relativeFunctorExtensionSpaceVertexEquiv p a i v hv ⟨W', hW', hWi'⟩)
  let q := relativeExtensionFiberEndpoint p a i v hv j b hj
  have he := relativeExtensionFiberEndpoint_witnessIso_heq_map p a i hi v hv j b hj
    W W' hW hW' hWi hWi' g g' hWj hWj'
  have hs := relativeExtensionFiberEndpoint_vertex p a i v hv j b hj W hW hWi g hWj
  have ht := relativeExtensionFiberEndpoint_vertex p a i v hv j b hj W' hW' hWi' g' hWj'
  have hm := vertexIso_map_heq_of_heq
    (relativeExtensionFiberEndpoint_witnessIso p a i hi v hv j b hj
      W W' hW hW' hWi hWi' g g' hWj hWj') (VertexIso.map e q) hs.symm ht.symm he
      ((pre s).app (vertexFiber p b))
  have hp : HEq ((relativeExtensionFiberEndpoint_witnessIso p a i hi v hv j b hj
      W W' hW hW' hWi hWi' g g' hWj hWj').precomp s)
      (VertexIso.map (VertexIso.map e q) ((pre s).app (vertexFiber p b))) := by
    simpa only [functorIso_precomp_eq_mapIso, VertexIso.map, hoFunctor_map,
      Functor.toCatHom_toFunctor] using hm
  have he' := relativeExtensionFiberEndpoint_witnessIso_heq_map p a i hi v hv (s ≫ j) b
    (by rw [Category.assoc, hj, SSet.comp_const]) W W' hW hW' hWi hWi' (s ≫ g) (s ≫ g')
    (by rw [Category.assoc, hWj, Category.assoc])
    (by rw [Category.assoc, hWj', Category.assoc])
  exact eq_of_heq (hp.trans
    ((heq_of_eq (vertexIso_map_comp e q ((pre s).app (vertexFiber p b)))).trans
      ((vertexIso_map_heq e
        (relativeExtensionFiberEndpoint_precomp p a i v hv j b hj s).symm).trans he'.symm)))

end SerrePositivity.InfinityCategories.F2
