module
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomPinched
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomPrismZero
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransPinchedSlice
public import SerrePositivity.InfinityCategories.Derived.DGStrictNatTransPointEdge

/-! # 閉前合成の全次数の固定標的 slice prism

概要：閉前合成した係数の標準 slice 表示と元の係数の表示を実ホモトピーで結ぶ。
方針：自由 Hom の厳密自然変換の prism に元の全係数単体を含め、両端を回収する。
規約：全ての面・退化と両端を厳密に保つ。使われ方：実屋根の細分輸送への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {p q : D} (y : D)
variable (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)

/-- 元の pinched Hom 全体に対する、閉前合成の指定標的 slice 内の実 prism。 -/
def dgClosedPrecompositionSlicePrism :
    DGNerve.pinchedHom A D q y ⊗ (Δ[1] : SSet.{max u v}) ⟶
      sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y)) :=
  (dgWalkingHomPinched A D q y ▷ Δ[1]) ≫
    dgStrictNatTransPinchedSlice A (DGWalkingHom.{u, v} A (homObject A D q y)) D
      (dgWalkingHomPrecomposeNatTrans A D y r)
      (dgWalkingHomSource A (homObject A D q y))
      (dgWalkingHomTarget A (homObject A D q y))

/-- 実 slice prism の零端点は、指定閉射の全次数の前合成による像。 -/
lemma dgClosedPrecompositionSlicePrism_zero :
    SSet.ι₀ ≫ dgClosedPrecompositionSlicePrism A D y r =
      pinchedClosedPrecomposition A D r ≫
        (pinchedHomSliceFiberIso (X := dgNerve A D)
          (Simplex.vertex p) (Simplex.vertex y)).hom ≫
        vertexFiberι (sliceOverProjection
          ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y)))
          (Simplex.vertex p) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change (joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := dgNerve A D)).symm
    ((dgWalkingHomPrecomposeNatTrans A D y r).simplex
      ((dgWalkingHomPinched A D q y).app (Opposite.op ⦋n⦌) s).val
      (pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (0 : Fin 2)))) =
    (joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := dgNerve A D)).symm
      (((pinchedClosedPrecomposition A D r).app (Opposite.op ⦋n⦌) s).val)
  exact congrArg (fun t => (joinStdSimplexIso n 0).hom ≫
    (SSet.yonedaEquiv (X := dgNerve A D)).symm t)
      ((dgWalkingHomPrism_zero A D y r _).trans
        (dgWalkingHomPinched_evaluation_val A D D q y p y (dgClosedPrecomposition A D r) s))

/-- 実 slice prism の一端点は、元の全係数の標準 slice 表示。 -/
lemma dgClosedPrecompositionSlicePrism_one :
    SSet.ι₁ ≫ dgClosedPrecompositionSlicePrism A D y r =
      (pinchedHomSliceFiberIso (X := dgNerve A D)
        (Simplex.vertex q) (Simplex.vertex y)).hom ≫
      vertexFiberι (sliceOverProjection
        ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y)))
        (Simplex.vertex q) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  let c := (dgWalkingHomPinched A D q y).app (Opposite.op ⦋n⦌) s
  let η := dgWalkingHomPrecomposeNatTrans A D y r
  change (joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := dgNerve A D)).symm
    (η.simplex c.val (pinchedPrismPhase (OrderHom.const (Fin (n + 1)) (1 : Fin 2)))) =
    (joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := dgNerve A D)).symm s.val
  have h := (congrArg (η.simplex c.val) (pinchedPrismPhase_one n)).trans (η.simplex_one c.val)
  have hval : c.val.map (dgWalkingHomOriginalEvaluation A D q y) = s.val := by
    have h' := dgWalkingHomPinched_evaluation_val A D D q y q y (𝟙 _) s
    have hid := congrArg (fun f => (f.app (Opposite.op ⦋n⦌) s).val)
      (pinchedHomChainMap_id (A := A) (D := D) (x := q) (y := y))
    exact h'.trans hid
  exact congrArg (fun t => (joinStdSimplexIso n 0).hom ≫
    (SSet.yonedaEquiv (X := dgNerve A D)).symm t) (h.trans hval)

/-- 閉前合成 prism の始域は、元の指定閉射の実辺に沿って動く。 -/
lemma dgClosedPrecompositionSlicePrism_source :
    dgClosedPrecompositionSlicePrism A D y r ≫ sliceOverProjection _ =
      snd (DGNerve.pinchedHom A D q y) Δ[1] ≫
        (SSet.yonedaEquiv (X := dgNerve A D)).symm (dgClosedEdge A D r).edge := by
  let η := dgWalkingHomPrecomposeNatTrans A D y r
  let j := dgWalkingHomPinched A D q y
  let f := dgStrictNatTransPointMap A (DGWalkingHom.{u, v} A (homObject A D q y)) D η
    (dgWalkingHomSource A (homObject A D q y))
  have h := congrArg (fun k => (j ▷ (Δ[1] : SSet.{max u v})) ≫ k)
    (dgStrictNatTransPinchedSlice_projection A (DGWalkingHom.{u, v} A (homObject A D q y)) D η
      (dgWalkingHomSource A (homObject A D q y))
      (dgWalkingHomTarget A (homObject A D q y)))
  calc
    _ = (j ▷ Δ[1]) ≫ snd _ Δ[1] ≫ f := by
      exact (Category.assoc _ _ _).trans h
    _ = snd (DGNerve.pinchedHom A D q y) Δ[1] ≫ f := by
      rw [← Category.assoc, whiskerRight_snd]
    _ = _ := congrArg (fun f => snd (DGNerve.pinchedHom A D q y) Δ[1] ≫ f)
      (dgStrictNatTransPointMap_edge A (DGWalkingHom.{u, v} A (homObject A D q y)) D η
        (dgWalkingHomSource A (homObject A D q y)))


end SerrePositivity.InfinityCategories
