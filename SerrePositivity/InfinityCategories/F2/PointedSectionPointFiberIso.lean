module

public import SerrePositivity.InfinityCategories.F2.PointedSectionTargetFiber

/-!
概要：共通終点上の切断空間を、元の同じ小さい fiber の持ち上げへ厳密に表示する。
方針：一点上の相対関手同型、明示した頂点等式、pointed fiber の縮小同型を合成する。
規約：底の頂点等式を入力に保持。使われ方：切断 cospan の共通終点の表示変更。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 底上の点制限を評価して含めると、元の族の同じ点評価になる。 -/
lemma relativeFunctorOverPre_point_ι {A E B : SSet.{u}} (p : E ⟶ B)
    (a : (Δ[0] : SSet.{u}) ⟶ B) (e : A ⟶ B) (j : (Δ[0] : SSet.{u}) ⟶ A)
    (hj : j ≫ e = a) :
    relativeFunctorOverPre p (Over.homMk (U := Over.mk a) (V := Over.mk e) j hj) ≫
        (relativePointFunctorIso p a).hom ≫
          vertexFiberι p (a.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) =
      relativeFunctorEvaluate p e (j.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)) ≫
        vertexFiberι p (e.app _ (j.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))) := by
  let r := relativeFunctorOverPre p (Over.homMk (U := Over.mk a) (V := Over.mk e) j hj)
  let ia := vertexFiberι ((ihom (Δ[0] : SSet.{u})).map p) (functorVertex a)
  let ie := vertexFiberι ((ihom A).map p) (functorVertex e)
  have hi : r ≫ ia = ie ≫ (pre j).app E := relativeFunctorOverPre_ι p _
  have h₀ : (relativePointFunctorIso p a).hom ≫ vertexFiberι p
      (a.app _ (stdSimplex.obj₀Equiv.symm 0)) =
      ia ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) :=
    relativeFunctorEvaluate_ι p a (stdSimplex.obj₀Equiv.symm 0)
  have h₁ := relativeFunctorEvaluate_ι p e
    (j.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0))
  exact (congrArg (fun k => r ≫ k) h₀).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)) hi).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun k => ie ≫ k)
        (evaluateFunctorAt_pre j (stdSimplex.obj₀Equiv.symm 0))).trans h₁.symm))))

variable {B : SSet.{u}}
  (J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
  (a : (Δ[0] : SSet.{u + 1}) ⟶ SpaceInfinity.{u})
  (ha : a.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) = J.app _ (ULift.up b))

/-- 共通点上の切断空間と、元の同じ小さい fiber の持ち上げとの厳密な同型。 -/
def pointedSectionPointFiberIso : relativeFunctorSpace pointedSpaceProjection a ≅
    coherentNativeTriangleFiberParameters J b :=
  relativePointFunctorIso pointedSpaceProjection a ≪≫
    eqToIso (congrArg (vertexFiber pointedSpaceProjection) ha) ≪≫
      (coherentFiberPointedSourceIso J b).symm

/-- この表示同型も、元の同じ点の pointed 全族を厳密に回収する。 -/
lemma pointedSectionPointFiberIso_pointed :
    (pointedSectionPointFiberIso J b a ha).hom ≫ coherentCospanFiberPointedSource J b =
      relativeFunctorEvaluate pointedSpaceProjection a (stdSimplex.obj₀Equiv.symm 0) ≫
        vertexFiberι pointedSpaceProjection (a.app _ (stdSimplex.obj₀Equiv.symm 0)) := by
  rw [← coherentFiberPointedSourceIso_hom_ι J b]
  simp only [pointedSectionPointFiberIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    Category.assoc, Iso.inv_hom_id_assoc, vertexFiberTransport_ι pointedSpaceProjection ha]
  rfl

end SerrePositivity.InfinityCategories.F2
