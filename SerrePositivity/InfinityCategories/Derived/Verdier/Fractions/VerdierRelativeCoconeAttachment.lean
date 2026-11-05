module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

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
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalPullbackColumnFamily s ≫ (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι =
      s ≫ (pre (CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) Δ[1])).app X := rfl

lemma terminalPullbackColumnFamily_source {P X : SSet.{u}} [Quasicategory X] [IsStable X]
    (s : P ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalPullbackColumnFamily s ≫ (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι ≫
      evaluateFunctorAt ((stdSimplex.obj₀Equiv.symm (0 : Fin 2)),
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
      s ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalPullbackColumnFamily_ι,
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
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalPullbackColumnFamily s := by
  apply (cancel_mono (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι).mp
  rw [Category.assoc, parametricPullbackDiagramFamily_evaluate_ι, hlast,
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalPullbackColumnFamily_ι]
  change internalHomFlipHomEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) P X
    (CartesianMonoidalCategory.snd Δ[1] Δ[1] ≫ internalHomFlipHomEquiv P Δ[1] X s) = _
  rw [internalHomFlipHomEquiv_pre]
  have he : internalHomFlipHomEquiv Δ[1] P X (internalHomFlipHomEquiv P Δ[1] X s) = s :=
    (internalHomFlipHomEquiv P Δ[1] X).symm_apply_apply s
  rw [he]

/-- 終端制限の全族一致は、同じ終端点評価の全族一致を含む。 -/
lemma terminalPullbackFamily_evaluate_of_restriction {P X : SSet.{u}} {n : ℕ}
    (F G : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X))
    (h : F ≫ (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X) =
      G ≫ (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X)) :
    F ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      G ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) := by
  have he := congrArg (fun f => f ≫
    (pointFunctorEvaluationIso (pullbackDiagrams X)).hom) h
  change (F ≫ (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X)) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
    (G ≫ (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X)) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) at he
  rw [Category.assoc, Category.assoc, stable_pre_evaluateFunctorAt] at he
  have hp : (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n).app (Opposite.op ⦋0⦌)
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
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalPullbackColumnFamily s) :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily F ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
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
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily, Category.assoc, hn, ← Category.assoc, hF,
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalPullbackColumnFamily_source]

/-- 元の実 span 全族の分母を、同じ実辺族として回収する。 -/
def verdierSpanFamilyDenominatorArrow {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B)
    (x z : B.obj _⦋0⦌) {P : SSet.{u}} (g : P ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x z) :
    P ⟶ (ihom (Δ[1] : SSet.{u})).obj B.obj :=
  g ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x z ≫ (verdierDenominatorOver i x).ι ≫
    F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm x)

/-- 元の実 span 全族の次辺を、同じ実辺族として回収する。 -/
def verdierSpanFamilyNumeratorArrow {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B)
    (x z : B.obj _⦋0⦌) {P : SSet.{u}} (g : P ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x z) :
    P ⟶ (ihom (Δ[1] : SSet.{u})).obj B.obj :=
  g ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanNumerator i x z ≫
    F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm z)

lemma verdierSpanFamilyArrows_sharedSource {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B)
    (x z : B.obj _⦋0⦌) {P : SSet.{u}} (g : P ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x z) :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i x z g ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z g ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyDenominatorArrow, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow,
    Category.assoc, Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanPointSliceArrowMap_source,
    Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanPointSliceArrowMap_source]
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpan_sharedSource]
  rfl

lemma verdierSpanFamilyNumeratorArrow_target {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B)
    (x z : B.obj _⦋0⦌) {P : SSet.{u}} (g : P ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x z) :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z g ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = SSet.const z := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow, Category.assoc, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanPointSliceArrowMap_target, SSet.comp_const, SSet.comp_const]
  congr 1
  have hp : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
  rw [hp, ← SSet.yonedaEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]

/-- 元の終端列から共有始域を証明し、同じ次辺円柱と指定部分族を全余錐へ厳密に貼る。 -/
lemma exists_relative_verdierSpanCoconeFamily
    {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) (x z : B.obj _⦋0⦌)
    {S P : SSet.{u}} {n : ℕ} (j : S ⟶ P) [Mono j]
    (g : P ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x z)
    (F : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams B.obj))
    (hF : F ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalPullbackColumnFamily (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i x z g))
    (a : S ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj)
    (ha : j ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily F =
      a ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj)
    (hb : j ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z g ≫
        (pre (joinStdSimplexIso 0 0).hom).app B.obj) =
      a ≫ (pre (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj) :
    ∃ L : P ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj,
      j ≫ L = a ∧
      L ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj = _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily F ∧
      L ≫ (pre (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
        _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z g ≫
          (pre (joinStdSimplexIso 0 0).hom).app B.obj ∧
      L ≫ evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z := by
  let N := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z g
  have hp : (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = stdSimplex.obj₀Equiv.symm (Fin.last n) := by
    have h₀ : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
    rw [h₀, ← SSet.yonedaEquiv_comp, Category.id_comp]
    exact Equiv.apply_symm_apply _ _
  have hleft : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily F ≫ (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app B.obj ≫
      (pointFunctorEvaluationIso B.obj).hom =
      N ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    change _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily F ≫ (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app B.obj ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = _
    rw [stable_pre_evaluateFunctorAt, hp, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily_last F _ hF]
    exact _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyArrows_sharedSource i x z g
  have hright : (N ≫ (pre (joinStdSimplexIso 0 0).hom).app B.obj) ≫
      (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app B.obj ≫
      (pointFunctorEvaluationIso B.obj).hom =
      N ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    change (N ≫ (pre (joinStdSimplexIso 0 0).hom).app B.obj) ≫
      (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app B.obj ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = _
    rw [Category.assoc, stable_pre_evaluateFunctorAt, stable_pre_evaluateFunctorAt]
    rfl
  have hcomm : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily F ≫ (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app B.obj =
      (N ≫ (pre (joinStdSimplexIso 0 0).hom).app B.obj) ≫
        (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app B.obj := by
    apply (cancel_mono (pointFunctorEvaluationIso B.obj).hom).mp
    simpa only [Category.assoc] using hleft.trans hright.symm
  obtain ⟨L, hjL, hprefix, hlast⟩ := _root_.SerrePositivity.InfinityCategories.Derived.Localization.exists_relative_simplexAttachmentFamily n j a
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily F) (N ≫ (pre (joinStdSimplexIso 0 0).hom).app B.obj)
    hcomm ha hb
  refine ⟨L, hjL, hprefix, hlast, ?_⟩
  have h := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanCoconeFamily_apex_of_lastArrow L N hlast
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow_target] at h
  exact h

/-- 相対 pullback 補完を実適用し、同じ実次辺を貼った全族と指定境界を同時に返す。 -/
lemma exists_relative_verdierSpanPullbackCoconeFamily
    {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) (x z : B.obj _⦋0⦌)
    {S P : SSet.{u}} {n : ℕ} (j : S ⟶ P) [Mono j]
    (g : P ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x z)
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj B.obj)) (hQ : IsPullbackSquare Q)
    (hlast : Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      squareColumnDiagram (internalHomFlipHomEquiv P Δ[1] B.obj
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i x z g)))
    (aF : S ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams B.obj))
    (hab : aF ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj) =
      j ≫ parametricPullbackDiagramFamily Q hQ ≫
        (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj))
    (hac : aF ≫ (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams B.obj) =
      j ≫ parametricPullbackDiagramFamily Q hQ ≫
        (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams B.obj))
    (a : S ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj)
    (ha : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily aF =
      a ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj)
    (hb : j ≫ (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z g ≫
        (pre (joinStdSimplexIso 0 0).hom).app B.obj) =
      a ≫ (pre (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj) :
    ∃ (F : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams B.obj))
      (L : P ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj),
      j ≫ F = aF ∧
      F ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj) =
        parametricPullbackDiagramFamily Q hQ ≫
          (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj) ∧
      F ≫ (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams B.obj) =
        parametricPullbackDiagramFamily Q hQ ≫
          (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams B.obj) ∧
      j ≫ L = a ∧
      L ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj = _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily F ∧
      L ≫ (pre (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
        _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z g ≫
          (pre (joinStdSimplexIso 0 0).hom).app B.obj ∧
      L ≫ evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z := by
  obtain ⟨F, hjF, hFp, hFt⟩ :=
    exists_relative_parametricPullbackDiagramFamily Q hQ j aF hab hac
  have hF : F ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalPullbackColumnFamily (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i x z g) :=
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalPullbackFamily_evaluate_of_restriction F
      (parametricPullbackDiagramFamily Q hQ) hFt).trans
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.parametricPullbackDiagramFamily_terminal_column Q hQ _ hlast)
  have hj : j ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily F = _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily aF := by
    rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily, ← Category.assoc, hjF]
    rfl
  obtain ⟨L, hjL, hLp, hLn, hLa⟩ :=
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_relative_verdierSpanCoconeFamily i x z j g F hF a (hj.trans ha) hb
  exact ⟨F, L, hjF, hFp, hFt, hjL, hLp, hLn, hLa⟩

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.attachmentStableFiniteLimits := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.attachmentStableFiniteLimits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.attachmentStableParameterFiniteLimits := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.attachmentStableParameterFiniteLimits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_relative_verdierSpanCoconeFamily := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_relative_verdierSpanCoconeFamily

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_relative_verdierSpanPullbackCoconeFamily := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_relative_verdierSpanPullbackCoconeFamily

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.parametricPullbackDiagramFamily_terminal_column := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.parametricPullbackDiagramFamily_terminal_column

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.pullbackSourcePrefixFamily := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.pullbackSourcePrefixFamily_last := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily_last

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalPullbackColumnFamily (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.terminalPullbackColumnFamily := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalPullbackColumnFamily

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.terminalPullbackColumnFamily_source := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalPullbackColumnFamily_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.terminalPullbackColumnFamily_ι := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalPullbackColumnFamily_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.terminalPullbackFamily_evaluate_of_restriction := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalPullbackFamily_evaluate_of_restriction

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanFamilyArrows_sharedSource := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyArrows_sharedSource

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyDenominatorArrow (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanFamilyDenominatorArrow := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyDenominatorArrow

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanFamilyNumeratorArrow := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanFamilyNumeratorArrow_target := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow_target

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.pullbackSourcePrefixFamily._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.pullbackSourcePrefixFamily.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.terminalPullbackColumnFamily._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalPullbackColumnFamily._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanFamilyDenominatorArrow.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyDenominatorArrow.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanFamilyNumeratorArrow.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow.eq_1
