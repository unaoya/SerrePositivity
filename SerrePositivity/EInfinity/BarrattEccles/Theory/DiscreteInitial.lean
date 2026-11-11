module

public import SerrePositivity.EInfinity.BarrattEccles.Theory
public import SerrePositivity.EInfinity.BarrattEccles.CAlgQuasiIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.StableLimits
public import SerrePositivity.EInfinity.Operad.AlgebraLift

/-!
# Barratt–Eccles 模型の離散基礎環は始対象

## 概要
HA §3.2.2 の初期代数を離散入力で実現する。

## 方針
導来自由代数を零複体で評価し、
厳密な自由代数の零入力部分を比較する。

## 規約
可換基礎環は任意で、離散基礎環は恒等構造射の像。

## 使われ方
Barratt–Eccles 実例の `discrete_initial`。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.TensorPowers
open scoped Simplicial ZeroObject

variable (A : Type u) [CommRing A]

/-- 零複体に対する Schur 図式の正の arity の値は零。 -/
lemma zero_schurDiagram_isZero (P : SymmetricSequence (Complex A)) (S : FiniteBijection)
    (h : S.card ≠ 0) :
    IsZero ((schurDiagram A P (0 : Complex A)).obj S) := by
  change IsZero (P.obj S ⊗ power (0 : Complex A) S.card)
  generalize S.card = n at h ⊢
  cases n with
  | zero => contradiction
  | succ n =>
    exact (tensorLeft (P.obj S)).map_isZero
      ((tensorRight (power (0 : Complex A) n)).map_isZero (isZero_zero (Complex A)))

/-- 零複体に対する Schur 対象は arity 0 の成分だけからなる。 -/
lemma schurι_zero_isIso (P : SymmetricSequence (Complex A)) :
    IsIso (schurι A P (0 : Complex A) 0) := by
  let F := schurDiagram A P (0 : Complex A)
  let b := FiniteBijection.of 0
  let e (S : FiniteBijection) (h : S.card = 0) : S = b :=
    (FiniteBijection.of_card S).symm.trans (congrArg FiniteBijection.of h)
  let r (S : FiniteBijection) : F.obj S ⟶ F.obj b :=
    if h : S.card = 0 then eqToHom (congrArg F.obj (e S h)) else 0
  have hr {S T : FiniteBijection} (f : S ⟶ T) : F.map f ≫ r T = r S := by
    have hst := FiniteBijection.card_eq_of_hom f
    by_cases h : S.card = 0
    · have hT := hst.symm.trans h
      have hs := e S h
      have ht := e T hT
      subst S
      subst T
      have hf : f = 𝟙 b := by
        apply (FiniteBijection.homEquiv b b).injective
        apply Equiv.ext
        intro a
        exact Fin.elim0 a
      simp [hf, r, b]
    · exact (zero_schurDiagram_isZero A P S h).eq_of_src _ _
  let t := schurDesc A P (0 : Complex A) (F.obj b) r hr
  have ht : schurι A P (0 : Complex A) 0 ≫ t = 𝟙 _ := by
    rw [schurι_desc]
    simp [r, b]
    rfl
  refine ⟨⟨t, ht, ?_⟩⟩
  apply schur_hom_ext A P (0 : Complex A)
  intro n
  cases n with
  | zero => rw [← Category.assoc, ht, Category.id_comp, Category.comp_id]
  | succ n => exact (zero_schurDiagram_isZero A P (FiniteBijection.of (n + 1))
      (Nat.succ_ne_zero n)).eq_of_src _ _

/-- 導来自由関手が導来圏の零頂点を始頂点へ送る。 -/
lemma derivedFreeAtZero_isInitial :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (atVertex (cAlgFreeDerived A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityZeroVertex A)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isInitialVertex_of_intervalMappingSpace_isContractibleKan
  intro y
  exact (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitMappingSpaceCondition_iff_interval (cAlgFreeForgetDerivedAdjunction A).unitHom).mp
    (cAlgFreeForgetDerivedAdjunction A).unitMappingSpaceCondition _ y).isContractibleKan_iff).mpr
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityZeroVertex_isZeroVertex A).1.intervalMappingSpace_isContractibleKan _)

/-- 零頂点での随伴の自由代数と同じ厳密 probe の比較。 -/
def derivedFreeAtZeroProbeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (derivedFreeProbeVertex A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityZeroVertex A))
      (atVertex (cAlgFreeDerived A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityZeroVertex A)) := by
  let x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityZeroVertex A
  let U := cAlgForgetDerived A
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection U x
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (derivedFreeProbeUnitCommaAdjunctionIso A x) p
  have h₀ := derivedFreeProbeUnitCommaVertex_target A x
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSectionVertex_target_const (A := Δ[0])
    (cAlgFreeForgetDerivedAdjunction A).unitHom x
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget_const] at h₁
  have ht' := congrArg (fun q : (Δ[0] : SSet.{u + 1}) ⟶ CAlg_R A => SSet.yonedaEquiv q) h₁
  simp only [SSet.yonedaEquiv_const] at ht'
  have ht : atVertex p (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSectionVertex (cAlgFreeForgetDerivedAdjunction A).unitHom x) =
      atVertex (cAlgFreeDerived A) x := ht'
  exact eqToIso (congrArg SSet.HomotopyCategory.mk h₀.symm) ≪≫ h ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk ht)

/-- 零複体の自由代数から離散基礎環へ向かう、空の生成元の指定射。 -/
def freeZeroToDiscrete :
    (operad A).freeAlgebra (0 : Complex A) ⟶
      (discreteAlgebraFunctor A).obj (CommAlgCat.of A A) :=
  Operad.Algebra.liftHom _ 0

/-- 離散基礎環への射は零入力での augmentation により擬同型。 -/
lemma freeZeroToDiscrete_quasiIso : QuasiIso (freeZeroToDiscrete A).hom := by
  let P := operad A
  let B := (discreteAlgebraFunctor A).obj (CommAlgCat.of A A)
  let j := schurι A P.sequence (0 : Complex A) 0
  have hj : IsIso j := schurι_zero_isIso A P.sequence
  apply (quasiIso_iff_comp_left j (freeZeroToDiscrete A).hom).mp
  have he : j ≫ (freeZeroToDiscrete A).hom = B.action 0 := by
    change j ≫ B.schurLift (0 : (0 : Complex A) ⟶ B.carrier) = B.action 0
    rw [Operad.Algebra.ι_schurLift]
    change (𝟙 (P.arity 0) ⊗ₘ 𝟙 (𝟙_ (Complex A))) ≫ B.action 0 = _
    rw [id_tensorHom, whiskerLeft_id, Category.id_comp]
  rw [he, discreteAlgebraFunctor_action]
  have hε : QuasiIso ((augmentation A).map.app (FiniteBijection.of 0)) :=
    augmentation_quasiIso A 0
  let F := CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)
  let p := ModuleCat.ofHom (Algebra.linearMap A A)
  have hp : IsIso p := by
    rw [show p = 𝟙 (ModuleCat.of A A) from rfl]
    infer_instance
  change QuasiIso (((augmentation A).map.app (FiniteBijection.of 0) ▷ 𝟙_ (Complex A)) ≫
    (λ_ (𝟙_ (Complex A))).hom ≫ Functor.LaxMonoidal.ε F ≫ F.map p)
  let q : P.arity 0 ⟶ 𝟙_ (Complex A) := (augmentation A).map.app (FiniteBijection.of 0)
  have hq : QuasiIso q := hε
  have hn := rightUnitor_naturality q
  rw [← unitors_equal] at hn
  have heq : (q ▷ 𝟙_ (Complex A)) ≫ (λ_ (𝟙_ (Complex A))).hom ≫
      Functor.LaxMonoidal.ε F ≫ F.map p =
      (ρ_ (P.arity 0)).hom ≫ q ≫ Functor.LaxMonoidal.ε F ≫ F.map p := by
    simpa only [Category.assoc] using
      congrArg (fun k => k ≫ Functor.LaxMonoidal.ε F ≫ F.map p) hn
  change QuasiIso ((q ▷ 𝟙_ (Complex A)) ≫ (λ_ (𝟙_ (Complex A))).hom ≫
    Functor.LaxMonoidal.ε F ≫ F.map p)
  rw [heq]
  infer_instance

/-- 零複体の cofibrant probe との比較を自由代数に移す。 -/
lemma freeZeroToProbe_quasiIso :
    QuasiIso (((operad A).freeAlgebraFunctor.map
      (0 : (0 : Complex A) ⟶ (ComplexLimits.framedLimitProbeFunctor A).obj 0)).hom) := by
  let := projectiveModelCategory A
  let := modelCategory A
  have := free_isLeftQuillen A
  let f : (0 : Complex A) ⟶ (ComplexLimits.framedLimitProbeFunctor A).obj 0 := 0
  let q := (ComplexLimits.framedLimitProbeComparisonNatTrans A).app 0
  have hq : QuasiIso q := ComplexLimits.framedLimitProbeComparison_quasiIso A 0
  have hcomp : QuasiIso (f ≫ q) := by
    rw [(isZero_zero (Complex A)).eq_of_src (f ≫ q) (𝟙 _)]
    infer_instance
  have hf : QuasiIso f := quasiIso_of_comp_right f q
  have hw : WeakEquivalence f := ⟨hf⟩
  have h0 : IsCofibrant (0 : Complex A) :=
    (isCofibrant_iff_of_isInitial (𝟙 (0 : Complex A)) (isZero_zero _).isInitial).mpr
      inferInstance
  have h1 : IsCofibrant ((ComplexLimits.framedLimitProbeFunctor A).obj 0) :=
    ComplexLimits.framedLimitProbe_cofibrant A 0
  exact (weakEquivalence_iff A _).mp (SerrePositivity.Quillen.map_weakEquivalence_of_cofibrant
    (operad A).freeAlgebraFunctor f)

/-- HA §3.2.2 の離散基礎環は既存の CAlg_R の始対象。 -/
lemma discreteCAlgUnderEmbedding_initial :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (atVertex (discreteCAlgUnderEmbedding A)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (𝟙 (CommRingCat.of A))))) := by
  let B := CommAlgCat.of A A
  let f := (operad A).freeAlgebraFunctor.map
    (0 : (0 : Complex A) ⟶ (ComplexLimits.framedLimitProbeFunctor A).obj 0)
  let e₁ := cAlgVertexIsoOfQuasiIso A f (freeZeroToProbe_quasiIso A)
  let e₂ := cAlgVertexIsoOfQuasiIso A (freeZeroToDiscrete A) (freeZeroToDiscrete_quasiIso A)
  have e₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      (cAlgVertex A ((freeProbeFunctor A).obj (0 : Complex A)))
      (atVertex (cAlgFreeDerived A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityZeroVertex A)) :=
    derivedFreeAtZeroProbeIso A
  have e₃ := discreteCAlgEmbedding_vertexIso A B
  have e₄ := discreteCAlgUnderComparisonIso A B
  exact (derivedFreeAtZero_isInitial A).of_vertexIso
    (e₀.symm ≪≫ e₁.symm ≪≫ e₂ ≪≫ e₃.symm ≪≫ e₄)

end SerrePositivity.EInfinity.BarrattEccles
