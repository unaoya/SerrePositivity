module

public import SerrePositivity.InfinityCategories.F1.CoherentCompositionNaturality

/-!
概要：豊穣射の合成を右 slice の全パラメーター付き prism として実現する。
方針：最後の頂点を固定した coherent 単体を join の標準同型で錐へ移す。
規約：時刻零で合成射、時刻一で二番目の射を与える。
使われ方：普遍 pointed-space 輸送と豊穣合成との比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：合成の coherent 単体の最後の頂点は Z。
方針：coherent nerve の零単体をその対象で比較する。
規約：二値ラベルと二つの Hom 単体は任意。
使われ方：右 slice の固定終点条件。 -/
lemma coherentCompositionSimplex_target {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2) :
    (SimplicialNerve C).map (PinchedHom.lastVertex n).op
      (coherentCompositionSimplex σ τ t) = coherentNerveVertex Z := by
  apply (coherentNerveVertexEquiv C).symm.injective
  change coherentCompositionObj X Y Z t (Fin.last (n + 1)) = Z
  exact coherentCompositionObj_last X Y Z n t

/-- 概要：合成の coherent 単体を終点 Z 上の錐へ移す。
方針：標準単体と右に点を加えた join の同型を合成する。
規約：前面は固定しない。
使われ方：右 slice への合成 prism の各単体。 -/
noncomputable def coherentCompositionSliceSimplex {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2) :
    (sliceOver (SSet.yonedaEquiv.symm (coherentNerveVertex Z))) _⦋n⦌ := by
  refine ⟨(joinStdSimplexIso n 0).hom ≫
    SSet.yonedaEquiv.symm (coherentCompositionSimplex σ τ t), ?_⟩
  rw [← Category.assoc, joinStdSimplexIso_rightPoint_inr,
    SSet.yonedaEquiv_symm_naturality_left, coherentCompositionSimplex_target]

/-- 概要：右 slice の合成単体は面・退化と整合する。
方針：join の標準同型の自然性と合成単体の自然性を使う。
規約：三つのパラメーターを同じ添字写像で引き戻す。
使われ方：合成 prism の単体的な自然性。 -/
lemma coherentCompositionSliceSimplex_naturality {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y Z : C} {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2) :
    (sliceOver (SSet.yonedaEquiv.symm (coherentNerveVertex Z))).map α.op
      (coherentCompositionSliceSimplex σ τ t) =
    coherentCompositionSliceSimplex ((SimplicialCategory.sHom X Y).map α.op σ)
      ((SimplicialCategory.sHom Y Z).map α.op τ) (t.comp α.toOrderHom) := by
  apply Subtype.ext
  change joinMap (stdSimplex.map α) (𝟙 Δ[0]) ≫
      ((joinStdSimplexIso n 0).hom ≫
        SSet.yonedaEquiv.symm (coherentCompositionSimplex σ τ t)) = _
  rw [← Category.assoc, joinStdSimplexIso_rightPoint_naturality, Category.assoc,
    SSet.yonedaEquiv_symm_naturality_left, coherentCompositionSimplex_naturality]
  rfl

/-- 概要：二つの豊穣射から右 slice への同時パラメーター付き合成 prism。
方針：切替時刻と二つの Hom 単体を錐単体へ送り、自然性で束ねる。
規約：Hom の宇宙を coherent nerve の宇宙へ持ち上げる。
使われ方：普遍輸送を豊穣合成と比較する標準の高次データ。 -/
noncomputable def coherentCompositionPrism {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y Z : C) :
    Δ[1] ⊗ ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⊗
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z)) ⟶
        sliceOver (SSet.yonedaEquiv.symm (coherentNerveVertex Z)) where
  app d := ↾fun a ↦ coherentCompositionSliceSimplex a.2.1.down a.2.2.down
    (stdSimplex.objEquiv a.1).toOrderHom
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro a
    exact (coherentCompositionSliceSimplex_naturality α.unop a.2.1.down a.2.2.down
      (stdSimplex.objEquiv a.1).toOrderHom).symm

/-- 概要：宇宙を持ち上げた二つの豊穣 Hom の合成射。
方針：各単体で ULift を戻して豊穣合成し、再び持ち上げる。
規約：coherent nerve と同じ宇宙の単体集合間の射。
使われ方：合成 prism の零端点の表示。 -/
noncomputable def coherentHomComposition {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y Z : C) :
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y) ⊗
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z) ⟶
        (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Z) where
  app d := ↾fun a ↦ ULift.up ((eComp SSet X Y Z).app d (a.1.down, a.2.down))
  naturality _ _ α := by
    apply ConcreteCategory.hom_ext
    intro a
    apply ULift.ext
    change (eComp SSet X Y Z).app _
      (((SimplicialCategory.sHom X Y).map α) a.1.down,
        ((SimplicialCategory.sHom Y Z).map α) a.2.down) = _
    have h := (eComp SSet X Y Z).naturality α
    exact congrArg (fun f ↦ f (a.1.down, a.2.down)) h

/-- 概要：合成 prism の零端点は合成射の右 Hom 比較。
方針：錐の元の coherent 単体に戻して零端点公式を使う。
規約：全次数の二つの Hom パラメーターを保つ。
使われ方：標準輸送の始点の同定。 -/
lemma coherentCompositionPrism_zero {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y Z : C) :
    prismEndpoint 0 _ ≫ coherentCompositionPrism X Y Z =
      coherentHomComposition X Y Z ≫ coherentHomComparison X Z ≫
        pinchedHomToSliceFiber _ _ ≫ vertexFiberι _ _ := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  change (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
    (coherentCompositionSimplex a.1.down a.2.down (OrderHom.const _ 0)) = _
  rw [coherentCompositionSimplex_zero]
  rfl

/-- 概要：合成 prism の一端点は二番目の射の右 Hom 比較。
方針：錐の元の coherent 単体に戻して一端点公式を使う。
規約：第一の Hom パラメーターは射影で落とす。
使われ方：標準輸送の終点の同定。 -/
lemma coherentCompositionPrism_one {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y Z : C) :
    prismEndpoint 1 _ ≫ coherentCompositionPrism X Y Z =
      snd _ _ ≫ coherentHomComparison Y Z ≫
        pinchedHomToSliceFiber _ _ ≫ vertexFiberι _ _ := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  change (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
    (coherentCompositionSimplex a.1.down a.2.down (OrderHom.const _ 1)) = _
  rw [coherentCompositionSimplex_one]
  rfl

end SerrePositivity.InfinityCategories
