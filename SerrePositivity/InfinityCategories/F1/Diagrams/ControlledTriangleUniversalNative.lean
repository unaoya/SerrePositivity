module

public import SerrePositivity.InfinityCategories.F1.Diagrams.ControlledTriangleCoherentEncoderDiagonal
public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleSeparatedConstantNative
public import SerrePositivity.InfinityCategories.F1.Diagrams.TriangleIntervalIsoEvaluation

/-!
概要：普遍再構成の長 Hom は、各 k・l で元の全 native Hom の同じ関手頂点を回収する。
方針：二切断の定値パラメーターを同じ点へ戻し、native path の区間同型を消去する。
規約：直接 path の値だけでなく、長 Hom の全区間を保持する。
使われ方：実 coherent encoder の full native Hom 回収。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma controlledTriangleUniversalLongHom_at_pair
    (X Z : KanObject.{u}) (K : SSet.{u + 1})
    (c : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
    (l : (controlledTriangleLongHomSpace X Z K c) _⦋0⦌) (k : K _⦋0⦌) :
    (controlledTriangleUniversalLongHom X Z K c).app (Opposite.op ⦋0⦌) (k, l) =
      (controlledTriangleLongHomValue l).app (Opposite.op ⦋0⦌) k := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (controlledTriangleUniversalLongHom_at_vertex X Z K c l) (Opposite.op ⦋0⦌)) k
  change (controlledTriangleUniversalLongHom X Z K c).app (Opposite.op ⦋0⦌)
    (k, PinchedHom.constant l 0) = _ at h
  rw [pinchedConstant_zero] at h
  exact h

/-- 元の実 L の全入力で、再構成した小さい長 Hom の全関手頂点を回収する。 -/
lemma controlledTriangleSeparatedExtension_native_value
    (X Y Z : KanObject.{u}) (K : SSet.{u + 1})
    (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
    (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))
    (l : (controlledTriangleLongHomSpace X Z K (controlledTriangleCompositeFamily X Y Z K f g)) _⦋0⦌)
    (k : K _⦋0⦌) :
    functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
      (triangleSeparatedLongHom (controlledTriangleSeparatedExtension X Y Z K f g)
        (PinchedHom.constant k 2) (PinchedHom.constant l 2)
        (OrderHom.id : Fin 3 →o Fin 3) (i := 0) rfl 2)) =
      (controlledTriangleLongHomValue l).app (Opposite.op ⦋0⦌) k := by
  let c := controlledTriangleCompositeFamily X Y Z K f g
  let q := controlledTriangleUniversalLongHom X Z K c
  have h := triangleSeparatedLongHom_constant
    (controlledTriangleSeparatedExtension X Y Z K f g)
    (uncurry (controlledTriangleUniversalInterval X Z K c))
    (controlledTriangleSeparatedExtension_diagonal X Y Z K f g) k l
    (OrderHom.id : Fin 3 →o Fin 3) (i := 0) rfl 2
  rw [triangleMiddleMap_identity] at h
  change (SSet.uliftFunctor.{u + 1, u}).map _ =
    lift (uliftTriangleNativePathIntervalIso.{u, u + 1}).hom (SSet.const (k, l)) ≫
      uncurry (q ≫ (pre (uliftTriangleNativePathIntervalIso.{u, u + 1}).inv).app _) at h
  rw [triangleIntervalIsoEvaluation] at h
  rw [h]
  let w : (K ⊗ controlledTriangleLongHomSpace X Z K c) _⦋0⦌ := (k, l)
  have hc := curry_app_vertex (uncurry q) w
  rw [curry_uncurry] at hc
  exact hc.symm.trans (controlledTriangleUniversalLongHom_at_pair X Z K c l k)

end SerrePositivity.InfinityCategories
