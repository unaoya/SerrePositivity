module

public import SerrePositivity.KST.LocalizingInvariants.ParametricPullbackFamilyTranspose
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.CoconeFamilyLastArrow
public import SerrePositivity.InfinityCategories.Derived.Localization.SimplexAttachmentFamilies

/-!
概要：相対 pullback 族の前段と元の実次辺の円柱を、指定部分族を保って貼る。
方針：終端列四角形から共有始域を厳密に回収し、実 attachment の相対 RLP を適用する。
規約：共有始域の整合は追加入力にせず、元の実 span の同じ始域から証明する。
使われ方：実分数の境界輸送を全余錐の実輸送へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

local instance attachmentStableFiniteLimits {X : SSet.{u}} [Quasicategory X] [IsStable X] :
    HasFiniteLimits X := hasFiniteLimits_of_isStable _

local instance attachmentStableParameterFiniteLimits {X P : SSet.{u}}
    [Quasicategory X] [IsStable X] :
    HasFiniteLimits ((ihom P).obj X) := hasFiniteLimits_functorCategory _ _

/-- 同じ実辺族を列四角形の元の全族へ写す。 -/
def terminalPullbackColumnFamily {P X : SSet.{u}} [Quasicategory X] [IsStable X]
    (s : P ⟶ (ihom (Δ[1] : SSet.{u})).obj X) : P ⟶ pullbackDiagrams X :=
  fullSubcomplexLift IsPullbackDiagramVertex
    (s ≫ (pre (CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) Δ[1])).app X) (by
      intro p
      obtain ⟨a, ha⟩ := (functorVertexEquiv (Δ[1] : SSet.{u}) X).surjective
        (s.app (Opposite.op ⦋0⦌) p)
      change IsPullbackDiagramVertex
        (((pre (CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) Δ[1])).app X).app
          (Opposite.op ⦋0⦌) (s.app (Opposite.op ⦋0⦌) p))
      rw [← ha]
      change IsPullbackSquare ((functorVertexEquiv _ X).symm
        ((functorVertexEquiv _ X) (squareColumnDiagram a)))
      rw [Equiv.symm_apply_apply]
      exact IsStable.pullback_of_pushout_square _ (squareColumnDiagram_isPushout a))

lemma terminalPullbackColumnFamily_ι {P X : SSet.{u}} [Quasicategory X] [IsStable X]
    (s : P ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    terminalPullbackColumnFamily s ≫ (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι =
      s ≫ (pre (CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) Δ[1])).app X := rfl

lemma terminalPullbackColumnFamily_source {P X : SSet.{u}} [Quasicategory X] [IsStable X]
    (s : P ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    terminalPullbackColumnFamily s ≫ (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι ≫
      evaluateFunctorAt ((stdSimplex.obj₀Equiv.symm (0 : Fin 2)),
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
      s ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [← Category.assoc, terminalPullbackColumnFamily_ι,
    Category.assoc, stable_pre_evaluateFunctorAt]
  rfl

/-- 元の全終端列を固定した正方形から、実 pullback 族の同じ終端列を厳密に回収する。 -/
lemma parametricPullbackDiagramFamily_terminal_column {P X : SSet.{u}}
    [Quasicategory X] [IsStable X] {n : ℕ}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj X)) (hQ : IsPullbackSquare Q)
    (s : P ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (hlast : Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      squareColumnDiagram (internalHomFlipHomEquiv P Δ[1] X s)) :
    parametricPullbackDiagramFamily Q hQ ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      terminalPullbackColumnFamily s := by
  apply (cancel_mono (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι).mp
  rw [Category.assoc, parametricPullbackDiagramFamily_evaluate_ι, hlast,
    terminalPullbackColumnFamily_ι]
  change internalHomFlipHomEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) P X
    (CartesianMonoidalCategory.snd Δ[1] Δ[1] ≫ internalHomFlipHomEquiv P Δ[1] X s) = _
  rw [internalHomFlipHomEquiv_pre]
  have he : internalHomFlipHomEquiv Δ[1] P X (internalHomFlipHomEquiv P Δ[1] X s) = s :=
    (internalHomFlipHomEquiv P Δ[1] X).symm_apply_apply s
  rw [he]

/-- 終端制限の全族一致は、同じ終端点評価の全族一致を含む。 -/
lemma terminalPullbackFamily_evaluate_of_restriction {P X : SSet.{u}} {n : ℕ}
    (F G : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X))
    (h : F ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams X) =
      G ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams X)) :
    F ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      G ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) := by
  have he := congrArg (fun f => f ≫
    (pointFunctorEvaluationIso (pullbackDiagrams X)).hom) h
  change (F ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams X)) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
    (G ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams X)) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) at he
  rw [Category.assoc, Category.assoc, stable_pre_evaluateFunctorAt] at he
  have hp : (simplexLastPoint n).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = stdSimplex.obj₀Equiv.symm (Fin.last n) := by
    have h₀ : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
    rw [h₀, ← SSet.yonedaEquiv_comp, Category.id_comp]
    exact Equiv.apply_symm_apply _ _
  rwa [hp] at he

/-- 全 pullback 族の同じ左下頂点からなる、精密化された実前段。 -/
def pullbackSourcePrefixFamily {P X : SSet.{u}} {n : ℕ}
    (F : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X)) :
    P ⟶ (ihom (Δ[n] : SSet.{u})).obj X :=
  F ≫ (ihom (Δ[n] : SSet.{u})).map
    ((fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι ≫
      evaluateFunctorAt ((stdSimplex.obj₀Equiv.symm (0 : Fin 2)),
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))

/-- 終端の列四角形を固定すると、精密化された前段の終端は元の分母族の始域。 -/
lemma pullbackSourcePrefixFamily_last {P X : SSet.{u}} [Quasicategory X] [IsStable X] {n : ℕ}
    (F : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X))
    (s : P ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (hF : F ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      terminalPullbackColumnFamily s) :
    pullbackSourcePrefixFamily F ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      s ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  have hn : (ihom (Δ[n] : SSet.{u})).map
      ((fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι ≫
        evaluateFunctorAt (Y := X) ((stdSimplex.obj₀Equiv.symm (0 : Fin 2)),
          (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) ≫
      (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι ≫
        evaluateFunctorAt (Y := X) ((stdSimplex.obj₀Equiv.symm (0 : Fin 2)),
          (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := rfl
  rw [pullbackSourcePrefixFamily, Category.assoc, hn, ← Category.assoc, hF,
    terminalPullbackColumnFamily_source]

/-- 元の実 span 全族の分母を、同じ実辺族として回収する。 -/
def verdierSpanFamilyDenominatorArrow {A B : StableCategory.{u}} (i : ExactMap A B)
    (x z : B.obj _⦋0⦌) {P : SSet.{u}} (g : P ⟶ verdierDenominatorSpanFamily i x z) :
    P ⟶ (ihom (Δ[1] : SSet.{u})).obj B.obj :=
  g ≫ verdierDenominatorSpanProjection i x z ≫ (verdierDenominatorOver i x).ι ≫
    F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm x)

/-- 元の実 span 全族の次辺を、同じ実辺族として回収する。 -/
def verdierSpanFamilyNumeratorArrow {A B : StableCategory.{u}} (i : ExactMap A B)
    (x z : B.obj _⦋0⦌) {P : SSet.{u}} (g : P ⟶ verdierDenominatorSpanFamily i x z) :
    P ⟶ (ihom (Δ[1] : SSet.{u})).obj B.obj :=
  g ≫ verdierDenominatorSpanNumerator i x z ≫
    F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm z)

lemma verdierSpanFamilyArrows_sharedSource {A B : StableCategory.{u}} (i : ExactMap A B)
    (x z : B.obj _⦋0⦌) {P : SSet.{u}} (g : P ⟶ verdierDenominatorSpanFamily i x z) :
    verdierSpanFamilyDenominatorArrow i x z g ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      verdierSpanFamilyNumeratorArrow i x z g ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [verdierSpanFamilyDenominatorArrow, verdierSpanFamilyNumeratorArrow,
    Category.assoc, Category.assoc, Category.assoc, spanPointSliceArrowMap_source,
    Category.assoc, Category.assoc, spanPointSliceArrowMap_source]
  rw [verdierDenominatorSpan_sharedSource]
  rfl

lemma verdierSpanFamilyNumeratorArrow_target {A B : StableCategory.{u}} (i : ExactMap A B)
    (x z : B.obj _⦋0⦌) {P : SSet.{u}} (g : P ⟶ verdierDenominatorSpanFamily i x z) :
    verdierSpanFamilyNumeratorArrow i x z g ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = SSet.const z := by
  rw [verdierSpanFamilyNumeratorArrow, Category.assoc, Category.assoc,
    spanPointSliceArrowMap_target, SSet.comp_const, SSet.comp_const]
  congr 1
  have hp : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
  rw [hp, ← SSet.yonedaEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]

/-- 元の終端列から共有始域を証明し、同じ次辺円柱と指定部分族を全余錐へ厳密に貼る。 -/
lemma exists_relative_verdierSpanCoconeFamily
    {A B : StableCategory.{u}} (i : ExactMap A B) (x z : B.obj _⦋0⦌)
    {S P : SSet.{u}} {n : ℕ} (j : S ⟶ P) [Mono j]
    (g : P ⟶ verdierDenominatorSpanFamily i x z)
    (F : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams B.obj))
    (hF : F ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      terminalPullbackColumnFamily (verdierSpanFamilyDenominatorArrow i x z g))
    (a : S ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj)
    (ha : j ≫ pullbackSourcePrefixFamily F =
      a ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj)
    (hb : j ≫ (verdierSpanFamilyNumeratorArrow i x z g ≫
        (pre (joinStdSimplexIso 0 0).hom).app B.obj) =
      a ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app B.obj) :
    ∃ L : P ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj,
      j ≫ L = a ∧
      L ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj = pullbackSourcePrefixFamily F ∧
      L ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
        verdierSpanFamilyNumeratorArrow i x z g ≫
          (pre (joinStdSimplexIso 0 0).hom).app B.obj ∧
      L ≫ evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z := by
  let N := verdierSpanFamilyNumeratorArrow i x z g
  have hp : (simplexLastPoint n).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = stdSimplex.obj₀Equiv.symm (Fin.last n) := by
    have h₀ : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
    rw [h₀, ← SSet.yonedaEquiv_comp, Category.id_comp]
    exact Equiv.apply_symm_apply _ _
  have hleft : pullbackSourcePrefixFamily F ≫ (pre (simplexLastPoint n)).app B.obj ≫
      (pointFunctorEvaluationIso B.obj).hom =
      N ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    change pullbackSourcePrefixFamily F ≫ (pre (simplexLastPoint n)).app B.obj ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = _
    rw [stable_pre_evaluateFunctorAt, hp, pullbackSourcePrefixFamily_last F _ hF]
    exact verdierSpanFamilyArrows_sharedSource i x z g
  have hright : (N ≫ (pre (joinStdSimplexIso 0 0).hom).app B.obj) ≫
      (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app B.obj ≫
      (pointFunctorEvaluationIso B.obj).hom =
      N ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    change (N ≫ (pre (joinStdSimplexIso 0 0).hom).app B.obj) ≫
      (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app B.obj ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = _
    rw [Category.assoc, stable_pre_evaluateFunctorAt, stable_pre_evaluateFunctorAt]
    rfl
  have hcomm : pullbackSourcePrefixFamily F ≫ (pre (simplexLastPoint n)).app B.obj =
      (N ≫ (pre (joinStdSimplexIso 0 0).hom).app B.obj) ≫
        (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app B.obj := by
    apply (cancel_mono (pointFunctorEvaluationIso B.obj).hom).mp
    simpa only [Category.assoc] using hleft.trans hright.symm
  obtain ⟨L, hjL, hprefix, hlast⟩ := exists_relative_simplexAttachmentFamily n j a
    (pullbackSourcePrefixFamily F) (N ≫ (pre (joinStdSimplexIso 0 0).hom).app B.obj)
    hcomm ha hb
  refine ⟨L, hjL, hprefix, hlast, ?_⟩
  have h := spanCoconeFamily_apex_of_lastArrow L N hlast
  rw [verdierSpanFamilyNumeratorArrow_target] at h
  exact h

/-- 相対 pullback 補完を実適用し、同じ実次辺を貼った全族と指定境界を同時に返す。 -/
lemma exists_relative_verdierSpanPullbackCoconeFamily
    {A B : StableCategory.{u}} (i : ExactMap A B) (x z : B.obj _⦋0⦌)
    {S P : SSet.{u}} {n : ℕ} (j : S ⟶ P) [Mono j]
    (g : P ⟶ verdierDenominatorSpanFamily i x z)
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj B.obj)) (hQ : IsPullbackSquare Q)
    (hlast : Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      squareColumnDiagram (internalHomFlipHomEquiv P Δ[1] B.obj
        (verdierSpanFamilyDenominatorArrow i x z g)))
    (aF : S ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams B.obj))
    (hab : aF ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj) =
      j ≫ parametricPullbackDiagramFamily Q hQ ≫
        (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj))
    (hac : aF ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams B.obj) =
      j ≫ parametricPullbackDiagramFamily Q hQ ≫
        (pre (simplexLastPoint n)).app (pullbackDiagrams B.obj))
    (a : S ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj)
    (ha : pullbackSourcePrefixFamily aF =
      a ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj)
    (hb : j ≫ (verdierSpanFamilyNumeratorArrow i x z g ≫
        (pre (joinStdSimplexIso 0 0).hom).app B.obj) =
      a ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app B.obj) :
    ∃ (F : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams B.obj))
      (L : P ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj),
      j ≫ F = aF ∧
      F ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj) =
        parametricPullbackDiagramFamily Q hQ ≫
          (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj) ∧
      F ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams B.obj) =
        parametricPullbackDiagramFamily Q hQ ≫
          (pre (simplexLastPoint n)).app (pullbackDiagrams B.obj) ∧
      j ≫ L = a ∧
      L ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj = pullbackSourcePrefixFamily F ∧
      L ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
        verdierSpanFamilyNumeratorArrow i x z g ≫
          (pre (joinStdSimplexIso 0 0).hom).app B.obj ∧
      L ≫ evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z := by
  obtain ⟨F, hjF, hFp, hFt⟩ :=
    exists_relative_parametricPullbackDiagramFamily Q hQ j aF hab hac
  have hF : F ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      terminalPullbackColumnFamily (verdierSpanFamilyDenominatorArrow i x z g) :=
    (terminalPullbackFamily_evaluate_of_restriction F
      (parametricPullbackDiagramFamily Q hQ) hFt).trans
        (parametricPullbackDiagramFamily_terminal_column Q hQ _ hlast)
  have hj : j ≫ pullbackSourcePrefixFamily F = pullbackSourcePrefixFamily aF := by
    rw [pullbackSourcePrefixFamily, ← Category.assoc, hjF]
    rfl
  obtain ⟨L, hjL, hLp, hLn, hLa⟩ :=
    exists_relative_verdierSpanCoconeFamily i x z j g F hF a (hj.trans ha) hb
  exact ⟨F, L, hjF, hFp, hFt, hjL, hLp, hLn, hLa⟩

end SerrePositivity.KST.LocalizingInvariants
