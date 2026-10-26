module

public import SerrePositivity.KST.LocalizingInvariants.IntervalMappingFamilyTranspose
public import SerrePositivity.KST.LocalizingInvariants.SimplexTerminalCoconeExtension
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeVertexTriangles

/-!
概要：同じ前段上の全余錐族を、パラメータ関手圏の元の全余錐へ移す。
方針：内部 Hom の厳密転置で前段と終端脚を保ち、比較同型も同じ交換で移す。
規約：終端脚は元の実辺の一次単体のまま回収する。
使われ方：回収した実分母・次辺を指定前段経路付きの全単体比較へ貼る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 二変数の同じ内部 Hom の交換による全関手同型の転置。 -/
def spanFunctorIsoFlip {K L X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ (ihom L).obj X} (e : FunctorIso F G) :
    FunctorIso (internalHomFlipHomEquiv K L X F) (internalHomFlipHomEquiv K L X G) := by
  have h := VertexIso.map e (internalHomSwapIso K L X).hom
  simp only [internalHomSwapIso_functorVertex] at h
  change FunctorIso (curry ((β_ K L).hom ≫ uncurry F))
    (curry ((β_ K L).hom ≫ uncurry G))
  exact h

/-- 前段が同じ図式に厳密に定値な余錐族を、関手圏の元の余錐へ移す。 -/
def spanCoconeFamilyTranspose {K L X : SSet.{u}} (D : L ⟶ X)
    (F : K ⟶ (ihom (join L (Δ[0] : SSet.{u}))).obj X)
    (hF : F ≫ (pre (joinInl L Δ[0])).app X = SSet.const (functorVertex D)) :
    JoinCocone (D ≫ curry (snd K X)) :=
  ⟨internalHomFlipHomEquiv K (join L Δ[0]) X F, by
    rw [← internalHomFlipHomEquiv_pre_app, hF, spanInternalHomFlip_const]⟩

/-- 同じ終端辺の全族から、転置した元の余錐の同じ終端脚を厳密に回収する。 -/
lemma spanCoconeFamilyTranspose_last_edge {K X : SSet.{u}} {n : ℕ}
    (D : (Δ[n] : SSet.{u}) ⟶ X)
    (F : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj X)
    (hF : F ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app X =
      SSet.const (functorVertex D))
    (a : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (ha : F ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app X =
      a ≫ (pre (joinStdSimplexIso 0 0).hom).app X) :
    (SerrePositivity.InfinityCategories.HomotopyLimits.coconeVertexLeg
      (spanCoconeFamilyTranspose D F hF) (SSet.yonedaEquiv (simplexLastPoint n))).edge =
      SSet.yonedaEquiv (internalHomFlipHomEquiv K Δ[1] X a) := by
  have he := congrArg (internalHomFlipHomEquiv K (join (Δ[0] : SSet.{u}) Δ[0]) X) ha
  rw [internalHomFlipHomEquiv_pre_app, internalHomFlipHomEquiv_pre_app] at he
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
    joinMap (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (simplexLastPoint n))) (𝟙 Δ[0]) ≫
      internalHomFlipHomEquiv K (join (Δ[n] : SSet.{u}) Δ[0]) X F) = _
  rw [Equiv.symm_apply_apply, he,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- 転置した同じ二つの全族の比較を、元の族の全関手同型へ戻す。 -/
def spanFunctorIsoUnflip {K L X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ (ihom L).obj X}
    (e : FunctorIso (internalHomFlipHomEquiv K L X F) (internalHomFlipHomEquiv K L X G)) :
    FunctorIso F G := by
  have h := spanFunctorIsoFlip e
  change FunctorIso
    ((internalHomFlipHomEquiv K L X).symm ((internalHomFlipHomEquiv K L X) F))
    ((internalHomFlipHomEquiv K L X).symm ((internalHomFlipHomEquiv K L X) G)) at h
  simpa only [Equiv.symm_apply_apply] using h

/-- 元の固定端点 Hom の族で指定した終端脚を、同じ実関手辺として回収する。 -/
lemma spanCoconeFamilyTranspose_last_interval_edge {K X : SSet.{u}} {n : ℕ}
    (D : (Δ[n] : SSet.{u}) ⟶ X)
    (F : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj X)
    (hF : F ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app X =
      SSet.const (functorVertex D)) {x y : X _⦋0⦌}
    (f : K ⟶ intervalMappingSpace x y)
    (hf : F ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app X =
      f ≫ vertexFiberι ((pre (boundary 1).ι).app X)
        (functorVertex (intervalMappingBoundary x y)) ≫
        (pre (joinStdSimplexIso 0 0).hom).app X) :
    (HomotopyLimits.coconeVertexLeg (spanCoconeFamilyTranspose D F hF)
      (SSet.yonedaEquiv (simplexLastPoint n))).edge = (intervalMappingFamilyEdge f).edge := by
  have he := spanCoconeFamilyTranspose_last_edge D F hF
    (f ≫ vertexFiberι ((pre (boundary 1).ι).app X)
      (functorVertex (intervalMappingBoundary x y))) hf
  exact he.trans (intervalMappingFamilyEdge_edge f).symm

/-- 元の前段比較を商後合成し、同じパラメータの定値図式間の実比較辺にする。 -/
def spanConstantPrefixEdge {L X Y : SSet.{u}} (K : SSet.{u}) (q : X ⟶ Y)
    {D E : L ⟶ X}
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom L).obj X))
      (functorVertex D) (functorVertex E)) :
    SSet.Edge (functorVertex (D ≫ q ≫ curry (snd K Y)))
      (functorVertex (E ≫ q ≫ curry (snd K Y))) :=
  (SSet.Edge.ofTruncated (X := (ihom L).obj X) t).map
    ((ihom L).map (q ≫ curry (snd K Y)))

lemma spanConstantPrefixEdge_component {L X Y : SSet.{u}} (K : SSet.{u}) (q : X ⟶ Y)
    {D E : L ⟶ X}
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom L).obj X))
      (functorVertex D) (functorVertex E)) (k : L _⦋0⦌) :
    (functorEdgeAt (spanConstantPrefixEdge K q t) k).edge =
      (curry (snd K Y)).app (Opposite.op ⦋1⦌)
        (q.app (Opposite.op ⦋1⦌)
          ((evaluateFunctorAt (Y := X) k).app (Opposite.op ⦋1⦌) t.edge)) := by
  have hn : (ihom L).map (q ≫ curry (snd K Y)) ≫
      evaluateFunctorAt (Y := (ihom K).obj Y) k =
      evaluateFunctorAt (Y := X) k ≫ q ≫ curry (snd K Y) := rfl
  exact ConcreteCategory.congr_hom (C := Type u)
    (NatTrans.congr_app hn (Opposite.op ⦋1⦌)) t.edge

lemma spanConstantPrefixEdge_isInvertible {L X Y : SSet.{u}} [Quasicategory Y]
    (K : SSet.{u}) (q : X ⟶ Y) {D E : L ⟶ X}
    (t : Truncated.Edge (X := (truncation 2).obj ((ihom L).obj X))
      (functorVertex D) (functorVertex E))
    (ht : IsInvertibleEdge (X := (ihom L).obj Y)
      (t.map ((truncation 2).map ((ihom L).map q)))) :
    IsInvertibleEdge (X := (ihom L).obj ((ihom K).obj Y))
      (spanConstantPrefixEdge K q t).toTruncated := by
  have hi := ht.map ((ihom L).map (curry (snd K Y)))
  exact (isInvertibleEdge_congr
    (e := (t.map ((truncation 2).map ((ihom L).map q))).map
      ((truncation 2).map ((ihom L).map (curry (snd K Y)))))
    (f := (spanConstantPrefixEdge K q t).toTruncated) rfl).mp hi

end SerrePositivity.KST.LocalizingInvariants
