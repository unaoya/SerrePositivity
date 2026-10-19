module

public import SerrePositivity.InfinityCategories.F1.CoherentCompositionFront
public import SerrePositivity.InfinityCategories.F1.MappingSpaceIntervalComparison

/-!
概要：右 prism による区間比較を coherent 単体の切断制限として計算する。
方針：標準単体への自然性と join の標準同型で一般の単体へ戻す。
規約：パラメーターは任意の単体集合。
使われ方：合成 prism の射影の全パラメーター付き同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右 prism に沿う任意の join 図式の評価は切断写像による制限。
方針：パラメーター単体の Yoneda 射に自然性を適用し、標準単体の場合へ帰着する。
規約：固定終点や quasicategory 性は要求しない。
使われ方：coherent Hom の区間比較の全単体での計算。 -/
lemma rightMappingSpacePrism_evaluate {A X : SSet.{u}} (F : join A Δ[0] ⟶ X)
    {n : ℕ} (a : A _⦋n⦌) (t : (Δ[1] : SSet.{u}) _⦋n⦌) :
    F.app (Opposite.op ⦋n⦌) ((rightMappingSpacePrism A).app (Opposite.op ⦋n⦌) (t, a)) =
      X.map (SimplexCategory.mkHom (coherentPrismCut (stdSimplex.objEquiv t).toOrderHom)).op
        (SSet.yonedaEquiv ((joinStdSimplexIso n 0).inv ≫
          joinMap (SSet.yonedaEquiv.symm a) (𝟙 Δ[0]) ≫ F)) := by
  let f := SSet.yonedaEquiv.symm a
  let g := joinMap f (𝟙 Δ[0]) ≫ F
  let b := (rightMappingSpacePrism Δ[n]).app (Opposite.op ⦋n⦌)
    (t, SSet.yonedaEquiv (𝟙 Δ[n]))
  have hn := congrArg (fun h ↦ h (t, SSet.yonedaEquiv (𝟙 Δ[n])))
    (NatTrans.congr_app (rightMappingSpacePrism_naturality f) (Opposite.op ⦋n⦌))
  change (rightMappingSpacePrism A).app (Opposite.op ⦋n⦌)
      (t, f.app (Opposite.op ⦋n⦌) (SSet.yonedaEquiv (𝟙 Δ[n]))) =
    (joinMap f (𝟙 Δ[0])).app (Opposite.op ⦋n⦌) b at hn
  rw [SSet.yonedaEquiv_symm_app_id] at hn
  rw [hn, ← SSet.yonedaEquiv_symm_app_objEquiv_symm, Equiv.symm_apply_apply]
  change g.app (Opposite.op ⦋n⦌) b = ((joinStdSimplexIso n 0).inv ≫ g).app
    (Opposite.op ⦋n⦌) _
  rw [← rightMappingSpacePrism_stdSimplex_cut n t]
  change g.app (Opposite.op ⦋n⦌) b =
    ((joinStdSimplexIso n 0).hom ≫ (joinStdSimplexIso n 0).inv ≫ g).app
      (Opposite.op ⦋n⦌) b
  rw [Iso.hom_inv_id_assoc]

/-- 概要：右 Hom の族を展開した join 図式の標準単体表示は元の pinched 単体。
方針：curry・uncurry の逆写像則を各単体で評価する。
規約：パラメーター単体も固定端点も任意。
使われ方：右 Hom の区間比較の元の coherent 単体への還元。 -/
lemma pinchedHomUncurry_simplex {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ pinchedHom x y) {n : ℕ} (a : A _⦋n⦌) :
    SSet.yonedaEquiv ((joinStdSimplexIso n 0).inv ≫
      joinMap (SSet.yonedaEquiv.symm a) (𝟙 Δ[0]) ≫ pinchedHomUncurry f) =
        (f.app (Opposite.op ⦋n⦌) a).val := by
  have h := congrArg (fun g : A ⟶ pinchedHom x y ↦
    (g.app (Opposite.op ⦋n⦌) a).val) (pinchedHomCurry_uncurry f)
  unfold pinchedHomCurry at h
  change ((pinchedHomSliceFiberIso x y).inv.app (Opposite.op ⦋n⦌) _).val = _ at h
  rw [pinchedHomSliceFiberIso_inv_app] at h
  exact h

/-- 概要：右 Hom の区間比較の評価は元の pinched 単体の切断制限。
方針：任意の join 図式の prism の公式へ curry・uncurry の座標を代入する。
規約：全次数のパラメーター単体を同時に扱う。
使われ方：coherent な合成 prism の射影の同定。 -/
lemma pinchedHomToIntervalMappingSpace_evaluate {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ pinchedHom x y) {n : ℕ} (a : A _⦋n⦌)
    (t : (Δ[1] : SSet.{u}) _⦋n⦌) :
    (intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace x y)).app
      (Opposite.op ⦋n⦌) (t, a) =
    X.map (SimplexCategory.mkHom (coherentPrismCut (stdSimplex.objEquiv t).toOrderHom)).op
      (f.app (Opposite.op ⦋n⦌) a).val := by
  rw [pinchedHomToIntervalMappingSpace_uncurry]
  change (pinchedHomUncurry f).app (Opposite.op ⦋n⦌)
    ((rightMappingSpacePrism A).app (Opposite.op ⦋n⦌) (t, a)) = _
  rw [rightMappingSpacePrism_evaluate, pinchedHomUncurry_simplex]

/-- 概要：合成 prism の射影は第一の射の既存の区間比較と一致する。
方針：各単体を前面に制限し、切断の coherent 単体の二つの表示を一致させる。
規約：第二の Hom パラメーターを含む全パラメーターの等式。
使われ方：右 slice の合成 prism を普遍輸送と比較するための底の式。 -/
lemma coherentCompositionPrism_projection {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y Z : C) :
    coherentCompositionPrism X Y Z ≫
      sliceOverProjection (SSet.yonedaEquiv.symm (coherentNerveVertex Z)) =
    (Δ[1] ◁ fst _ _) ≫ intervalMappingUncurry
      (coherentHomComparison X Y ≫ pinchedHomToIntervalMappingSpace _ _) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, σ, τ⟩
  change SSet.yonedaEquiv (joinInl Δ[n] Δ[0] ≫ (joinStdSimplexIso n 0).hom ≫
    SSet.yonedaEquiv.symm (coherentCompositionSimplex σ.down τ.down
      (stdSimplex.objEquiv t).toOrderHom)) = _
  rw [← Category.assoc, joinStdSimplexIso_rightPoint_inl,
    SSet.yonedaEquiv_symm_naturality_left, Equiv.apply_symm_apply,
    coherentCompositionSimplex_front]
  exact (pinchedHomToIntervalMappingSpace_evaluate (coherentHomComparison X Y) σ t).symm

end SerrePositivity.InfinityCategories
