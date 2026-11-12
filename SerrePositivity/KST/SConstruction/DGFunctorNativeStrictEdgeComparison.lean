module
public import SerrePositivity.KST.SConstruction.DGNativeIntervalAugmentation
public import SerrePositivity.KST.SConstruction.DGFunctorNativeEvaluationPoint
public import SerrePositivity.KST.SConstruction.DGStrictNatTransHomEnd
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NatTrans
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin

/-!
概要：元厳密 dg 変換の全 end 辺の native 評価を、同じ指定ホモトピーへ厳密照合する。
方針：元区間全 Hom の増大表示と同時評価を、全 HA 成分で計算する。
規約：頂点別一致や core 制限で代用せず、元変換・全次数・退化を保持。
使われ方：元 cone 全二単体と元 LT counit の逆回転との全比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open DifferentialGraded InfinityCategories
open scoped Simplicial

/-- 概要：全 end の単位からの係数挿入を同じ全次数評価へ送る。
方針：元逆単位射と tensor 純斉次元の評価則を使う。
規約：元閉係数を保持。使われ方：元区間係数の全評価。 -/
lemma dgFunctorTensorEvalHom_unitInsertion (R : Type u) [CommRing R]
    (D : Type v) [DGCategory R D] [Small.{u} D]
    (E : Type w) [DGCategory R E] {F G : DGFunctor R D E}
    {x y : D} (b : 𝟙_ (Complex R) ⟶ dgFunctorHom R D E F G)
    {p : ℤ} (a : GradedHom R x y p) :
    (dgFunctorTensorEvalHom R D E (x, F) (y, G)).f p
      (((ρ_ (homObject R D x y)).inv ≫ (𝟙 _ ⊗ₘ b)).f p a) =
      forward R ((F.map x y).f p a)
        ((dgFunctorHomπ R D E F G y).f 0 (cycleFromUnit _ b).val) (add_zero p) := by
  change (dgFunctorTensorEvalHom R D E (x, F) (y, G)).f p
    ((𝟙 _ ⊗ₘ b).f p ((ρ_ (homObject R D x y)).inv.f p a)) = _
  have hρ := complexRightUnitor_inv_apply (homObject R D x y) p a
  apply (congrArg (fun z => (dgFunctorTensorEvalHom R D E (x, F) (y, G)).f p
    ((𝟙 (homObject R D x y) ⊗ₘ b).f p z)) hρ).trans
  have ht := tensorMap_apply (𝟙 (homObject R D x y)) b p 0 p (add_zero p) a
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat R))).inv (1 : R))
  apply (congrArg (fun z => (dgFunctorTensorEvalHom R D E (x, F) (y, G)).f p z) ht).trans
  exact dgFunctorTensorEvalHom_element R D E
    (x := ((x, F) : DGTensorCategory R D (DGFunctor R D E)))
    (y := ((y, G) : DGTensorCategory R D (DGFunctor R D E)))
    a (cycleFromUnit _ b).val (add_zero p)

/-- 概要：元 end 区間の同じ係数評価は元厳密変換の二相作用そのもの。
方針：元単位・元閉成分を同じ全 end から回収する。
規約：全入力次数を保持。使われ方：全 HA 成分の照合。 -/
lemma dgStrictNatTransEndCoefficient_evaluation (R : Type u) [CommRing R] (D E : Type (u + 1))
    [DGCategory R D] [Small.{u} D] [DGCategory R E]
    {F G : DGFunctor R D E} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
    (p q : Fin 2) (hm : p ≤ q) {x y : D} {k : ℤ} (a : GradedHom R x y k) :
    HEq (forward R (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj F G p).map x y).f k a)
      ((dgFunctorHomπ R D E (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj F G p)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj F G q) y).f 0
        (cycleFromUnit _ (simplexHAEdgeCoefficient R (DGFunctor R D E)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj F G)
            (dgStrictNatTransEndCycle R D E η)) p q)).val) (add_zero k))
      (η.transition p q hm a) := by
  fin_cases p <;> fin_cases q
  · change HEq (forward R ((F.map (x) (y)).f k _)
      ((dgFunctorHomπ R D E F F (y)).f 0 (unitElement R F).val) (add_zero k)) _
    have hf := DGFunctor.map_unitElement R (dgFunctorEvaluationDG R D E (y)) F
    change (dgFunctorHomπ R D E F F (y)).f 0 (unitElement R F).val =
      (unitElement R (F.obj (y))).val at hf
    rw [hf]
    apply heq_of_eq
    change forward R ((F.map x y).f k a) (unitElement R (F.obj y)).val (add_zero k) =
      (F.map x y).f k a
    simpa only [compose, mul_zero, Int.negOnePow_zero, one_smul] using
      unit_compose R ((F.map x y).f k a)
  · change HEq (forward R ((F.map (x) (y)).f k _)
      ((dgFunctorHomπ R D E F G (y)).f 0
        (cycleFromUnit _ (unitFromCycle _
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj F G)
            (dgStrictNatTransEndCycle R D E η)).edgeCycle 0 1 (by decide)))).val)
      (add_zero k)) _
    rw [cycleFromUnit_unitFromCycle, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeCycle_ofEdge]
    change HEq (forward R ((F.map (x) (y)).f k _)
      ((dgFunctorHomπ R D E F G (y)).f 0
        (dgStrictNatTransEndElement R D E η)) (add_zero k)) _
    rw [dgStrictNatTransEndElement_π]
    apply heq_of_eq
    change forward R ((F.map x y).f k a) (η.app y).val (add_zero k) =
      compose R (η.app y).val ((F.map x y).f k a) (add_zero k)
    simp only [compose, mul_zero, Int.negOnePow_zero, one_smul]
  · change (1 : Fin 2) ≤ 0 at hm
    exact ((by decide : ¬ (1 : Fin 2) ≤ 0) hm).elim
  · change HEq (forward R ((G.map (x) (y)).f k _)
      ((dgFunctorHomπ R D E G G (y)).f 0 (unitElement R G).val) (add_zero k)) _
    have hf := DGFunctor.map_unitElement R (dgFunctorEvaluationDG R D E (y)) G
    change (dgFunctorHomπ R D E G G (y)).f 0 (unitElement R G).val =
      (unitElement R (G.obj (y))).val at hf
    rw [hf]
    apply heq_of_eq
    change forward R ((G.map x y).f k a) (unitElement R (G.obj y)).val (add_zero k) =
      (G.map x y).f k a
    simpa only [compose, mul_zero, Int.negOnePow_zero, one_smul] using
      unit_compose R ((G.map x y).f k a)

/-- 概要：元 end 辺の同時 native 評価は元二相ホモトピーの全単体。
方針：全部分集合成分で元増大表示・同時評価・元 HA 逆律を使う。
規約：全単体次数・退化・元成分の厳密等号。使われ方：元全ホモトピーの回収。 -/
lemma dgFunctorNativeStrictNatTrans_simplex (R : Type u) [CommRing R] (D E : Type (u + 1))
    [DGCategory R D] [Small.{u} D] [DGCategory R E]
    {F G : DGFunctor R D E} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
    {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D N) (β : Fin (N + 1) →o Fin 2) :
    (dgNerveTensorSimplex R s
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj F G)
        (dgStrictNatTransEndCycle R D E η)).pullback β)).map
          (dgFunctorTensorEvaluation R D E) = η.simplex s β := by
  unfold dgNerveTensorSimplex
  rw [simplexHAInverseFunctor_pullback]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · funext a
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj F G (β a)).obj (s.obj a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj F G (β a) (s.obj a)
    generalize β a = i
    fin_cases i <;> rfl
  · apply Function.hfunext rfl
    intro I I' h
    cases h
    apply Function.hfunext rfl
    intro a a' h
    cases h
    apply Function.hfunext rfl
    intro b b' h
    cases h
    apply Function.hfunext rfl
    intro k k' h
    cases h
    apply Function.hfunext rfl
    intro hI hI' h
    cases h
    apply Function.hfunext rfl
    intro ha ha' h
    cases h
    apply Function.hfunext rfl
    intro hb hb' h
    cases h
    apply Function.hfunext rfl
    intro hk hk' h
    cases h
    subst a b k
    let a₀ := I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)
    let b₀ := I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)
    let k₀ : ℤ := 2 - (I.card : ℤ)
    let e := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj F G)
      (dgStrictNatTransEndCycle R D E η)
    let l := simplexHAInverseFunctor R s
    let g := DGFunctor.comp
      (cubicalLambdaMap R (SSet.stdSimplex.map (SimplexCategory.Hom.mk β)))
      (simplexHAInverseFunctor R e)
    have hp := cubicalLambdaFunctorPair_edgeBaseChange R D (DGFunctor R D E)
      e l (SSet.stdSimplex.map (SimplexCategory.Hom.mk β))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a₀) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b₀)
    let z := simplexSubsetLambdaGenerator R I hI
    change HEq
      ((dgFunctorTensorEvalHom R D E
        (l.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a₀), g.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a₀))
        (l.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b₀), g.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b₀))).f k₀
        (((cubicalLambdaFunctorPair R l g).map
          (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a₀) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b₀)).f k₀ z))
      (η.transition (β a₀) (β b₀) _ (s.hom I a₀ b₀ k₀ hI rfl rfl rfl))
    have hc := congrArg (fun f => (dgFunctorTensorEvalHom R D E
      (l.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a₀), g.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a₀))
      (l.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b₀), g.obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b₀))).f k₀ (f.f k₀ z)) hp
    apply (heq_of_eq hc).trans
    change HEq
      ((dgFunctorTensorEvalHom R D E
        (s.obj a₀, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj F G (β a₀))
        (s.obj b₀, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj F G (β b₀))).f k₀
        (((ρ_ (homObject R D (s.obj a₀) (s.obj b₀))).inv ≫
          (𝟙 _ ⊗ₘ simplexHAEdgeCoefficient R (DGFunctor R D E) e (β a₀) (β b₀))).f k₀
          ((l.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a₀) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b₀)).f k₀ z)))
      (η.transition (β a₀) (β b₀) _ (s.hom I a₀ b₀ k₀ hI rfl rfl rfl))
    have hu := dgFunctorTensorEvalHom_unitInsertion R D E
      (F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj F G (β a₀))
      (G := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj F G (β b₀))
      (x := s.obj a₀) (y := s.obj b₀)
      (simplexHAEdgeCoefficient R (DGFunctor R D E) e (β a₀) (β b₀))
      ((l.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a₀) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b₀)).f k₀ z)
    apply (heq_of_eq hu).trans
    have hs : (l.map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a₀) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b₀)).f k₀ z =
        s.hom I a₀ b₀ k₀ hI rfl rfl rfl :=
      simplexHAInverseFunctor_native_hom R s I a₀ b₀ k₀ hI rfl rfl rfl
    rw [hs]
    exact dgStrictNatTransEndCoefficient_evaluation R D E η (β a₀) (β b₀)
      (β.monotone (I.min'_le _ (I.max'_mem _))) (s.hom I a₀ b₀ k₀ hI rfl rfl rfl)

/-- 概要：元 end 辺の全パラメータ評価は元厳密変換の指定ホモトピー写像。
方針：元一単体の Yoneda 表示を全入力単体で評価する。
規約：全写像の厳密等号。使われ方：元関手圏の同じ辺の回収。 -/
lemma dgFunctorNativeStrictNatTrans_homotopyMap (R : Type u) [CommRing R]
    (D E : Type (u + 1)) [DGCategory R D] [Small.{u} D] [DGCategory R E]
    {F G : DGFunctor R D E} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) :
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) ⊗ₘ
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R D E)) (n := ⦋1⦌)).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj F G) (dgStrictNatTransEndCycle R D E η))) ≫
      dgFunctorNativeEvaluation R D E = η.homotopyMap := by
  ext n p
  rcases p with ⟨s, a⟩
  change (dgNerveTensorSimplex R s
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj F G)
      (dgStrictNatTransEndCycle R D E η)).pullback
        (SSet.stdSimplex.objEquiv a).toOrderHom)).map
          (dgFunctorTensorEvaluation R D E) = _
  exact dgFunctorNativeStrictNatTrans_simplex R D E η s _

/-- 概要：元全 end の native 辺は旧厳密変換の指定ホモトピーの同じ全関手辺。
方針：同じ全パラメータ写像の等号を curry と Yoneda で戻す。
規約：全写像空間内の辺等号。使われ方：元 cone 面の指定境界照合。 -/
lemma dgFunctorNativeStrictNatTrans_edge (R : Type u) [CommRing R]
    (D E : Type (u + 1)) [DGCategory R D] [Small.{u} D] [DGCategory R E]
    {F G : DGFunctor R D E} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) :
    (dgFunctorNativeFullFamilyMap R D E).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj F G) (dgStrictNatTransEndCycle R D E η)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy η.homotopy).edge := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ofEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pairObj F G) (dgStrictNatTransEndCycle R D E η)
  let i : (Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R D E) :=
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R D E)) (n := ⦋1⦌)).symm e
  have hm : ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) ◁ i) ≫ dgFunctorNativeEvaluation R D E = η.homotopyMap :=
    dgFunctorNativeStrictNatTrans_homotopyMap R D E η
  have h : i ≫ dgFunctorNativeFullFamilyMap R D E = curry η.homotopyMap :=
    (curry_natural_left i (dgFunctorNativeEvaluation R D E)).symm.trans
      (congrArg (fun fm : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) ⊗ (Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E =>
        curry fm) hm)
  have he := congrArg (SSet.yonedaEquiv (X := (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E))
    (n := ⦋1⦌)) h
  have hi : SSet.yonedaEquiv i = e :=
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGFunctor R D E)) (n := ⦋1⦌)).apply_symm_apply e
  exact (congrArg ((dgFunctorNativeFullFamilyMap R D E).app (Opposite.op ⦋1⦌)) hi.symm).trans
    ((SSet.yonedaEquiv_comp i (dgFunctorNativeFullFamilyMap R D E)).symm.trans he)

end SerrePositivity.KST.SConstruction
