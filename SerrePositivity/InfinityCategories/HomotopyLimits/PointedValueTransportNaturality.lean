module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PointedRightTransportNaturality

/-!
概要：既存の pointed fiber の値比較は、元の Kan 射と coherent 辺の輸送に自然。
方針：同じ右 Hom の比較の自然性を、既存の値比較との両逆で共役する。
規約：元の値比較を新しい同値に置き換えない。使われ方：元の余錐の全 Hom の反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の辺の始点表示だけを変えた輸送は、元の fiber の標準移送を前合成した射。 -/
lemma edgeTransport_changeSource {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    {a a' b : B _⦋0⦌} (h : a = a') (e : SSet.Edge a b) :
    edgeTransport p (e.ofEq h rfl) =
      eqToHom (congrArg (vertexFiber p) h.symm) ≫ edgeTransport p e := by
  subst a'
  have he : e.ofEq rfl rfl = e := by
    apply SSet.Edge.ext
    rfl
  rw [he, eqToHom_refl, Category.id_comp]

/-- 既存の値比較は、元の射の持ち上げと元の coherent 辺の普遍輸送を全 fiber 上で結ぶ。 -/
def pointedValue_transportIso {K L : KanObject.{u}} (f : K ⟶ L) :
    FunctorIso
      ((pointedSpaceFiberValueEquivalence (spaceInfinityVertex K)).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map f)
      (edgeTransport pointedSpaceProjection (pointedRightMorphismEdge f) ≫
        (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom) := by
  let a := (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K)).hom
  let b := (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom
  let m := (SSet.uliftFunctor.{u + 1, u}).map f
  let t := edgeTransport pointedSpaceProjection (pointedRightMorphismEdge f)
  have e := ((pointedRightFiberComparison_transportIso f).precomp a).postcomp b
  have hl : FunctorIso (a ≫ m ≫ pointedRightFiberComparison L ≫ b) (a ≫ m) := by
    simpa only [pointedValueRightComparison_standard, Category.assoc, Category.comp_id] using
      (pointedValueRightComparison_counitIso (spaceInfinityVertex L)).precomp (a ≫ m)
  have hr : FunctorIso (a ≫ pointedRightFiberComparison K ≫ t ≫ b) (t ≫ b) := by
    simpa only [pointedValueRightComparison_standard, Category.assoc, Category.id_comp] using
      (pointedValueRightComparison_unitIso (spaceInfinityVertex K)).postcomp (t ≫ b)
  have he : FunctorIso (a ≫ m ≫ pointedRightFiberComparison L ≫ b)
      (a ≫ pointedRightFiberComparison K ≫ t ≫ b) := by
    simpa only [Category.assoc] using e
  exact hl.symm ≪≫ he ≪≫ hr

end SerrePositivity.InfinityCategories.HomotopyLimits
