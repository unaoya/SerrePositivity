module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.PullbackFamilySquareRecovery
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierParametricSourceIso

/-!
概要：回収済みの実余錐円柱から、元の終端分母経路を保持する同じ実前段正方形を戻す。
方針：保存済みの二脚一致を逆転置へ代入し、同じ右辺と pullback 性で左辺の分母性を証明。
規約：実補完・余錐円柱・分母経路を選び直さず、全写像と一次単体を保持する。
使われ方：境界上の全比較に、元の実分数評価正方形と共有する源経路を供給する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

local instance cylinderSquareFiniteLimits {X : SSet.{u}} [Quasicategory X] [IsStable X] :
    HasFiniteLimits X := hasFiniteLimits_of_isStable _

local instance cylinderSquareParameterFiniteLimits {X P : SSet.{u}}
    [Quasicategory X] [IsStable X] : HasFiniteLimits ((ihom P).obj X) :=
  hasFiniteLimits_functorCategory _ _

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj}
  {z : B.obj _⦋0⦌} {K : SSet.{u}} {S : K.Subcomplex}
  {a : S.toSSet ⟶ verdierDenominatorSpanFamily i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z}
  {f : K ⟶ intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌)
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (q.hom.app (Opposite.op ⦋0⦌) z)}

/-- 同じ実余錐円柱の補完済み pullback 全族から厳密に戻した全正方形。 -/
def VerdierFiniteMappingCoconeRecovery.cylinderSquare
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      (ihom (Δ[n] : SSet.{u})).obj ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj B.obj) :=
  pullbackFamilySquare r.cylinder.pullbacks

lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_isPullback
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    IsPullbackSquare r.cylinderSquare := pullbackFamilySquare_isPullback _

/-- 元の実円柱の始端正方形は、保存済みの同じ一つの pullback 補完の一様正方形。 -/
lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_start
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    r.cylinderSquare ≫ (ihom (Δ[n] : SSet.{u})).map
        ((pre (SSet.ι₀ : S.toSSet ⟶ S.toSSet ⊗ (Δ[1] : SSet.{u}))).app B.obj) =
      uniformTerminalRefinementSquare S.toSSet r.cylinder.single := by
  change pullbackFamilySquare r.cylinder.pullbacks ≫ _ = _
  rw [← pullbackFamilySquare_pre_parameter, r.cylinder.pullbacks_start]
  have he := congrArg (fun F : S.toSSet ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams B.obj) =>
    pullbackFamilySquare F) (uniformTerminalRefinementSquare_family S.toSSet r.cylinder.single)
  rw [pullbackFamilySquare_parametric] at he
  exact he.symm

/-- 元の実円柱の終端正方形も、保存済みの同じ正規化終端正方形に厳密一致する。 -/
lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_end
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    r.cylinderSquare ≫ (ihom (Δ[n] : SSet.{u})).map
        ((pre (SSet.ι₁ : S.toSSet ⟶ S.toSSet ⊗ (Δ[1] : SSet.{u}))).app B.obj) =
      r.cylinder.endSquare := by
  change pullbackFamilySquare r.cylinder.pullbacks ≫ _ = _
  rw [← pullbackFamilySquare_pre_parameter, r.cylinder.pullbacks_end,
    pullbackFamilySquare_parametric]

lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_right
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    squareRightEdge ≫ r.cylinderSquare = squareRightEdge ≫ r.square :=
  pullbackFamilySquare_right_eq _ _ _ r.cylinder.pullbacks_projection

lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_top
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    squareTopEdge ≫ r.cylinderSquare = squareTopEdge ≫ r.square :=
  pullbackFamilySquare_top_eq _ _ _ r.cylinder.pullbacks_projection

lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_original
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    squareVertex r.cylinderSquare 0 1 =
      functorVertex (D ≫ constantFunctorMap (S.toSSet ⊗ (Δ[1] : SSet.{u})) B.obj) := by
  change (squareTopEdge ≫ r.cylinderSquare).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = _
  rw [r.cylinderSquare_top]
  exact r.square_original

lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_terminal
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    r.cylinderSquare ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      squareColumnDiagram (internalHomFlipHomEquiv (S.toSSet ⊗ (Δ[1] : SSet.{u})) Δ[1] B.obj
        (verdierSpanFamilyDenominatorArrow i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z r.boundary.h)) :=
  (pullbackFamilySquare_last_eq _ _ _ r.cylinder.pullbacks_terminal).trans r.square_terminal

/-- 同じ実前段の左辺は、終端で元の実分母経路そのものに厳密に一致する。 -/
lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_terminal_left
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    squareLeftEdge ≫ r.cylinderSquare ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      internalHomFlipHomEquiv (S.toSSet ⊗ (Δ[1] : SSet.{u})) Δ[1] B.obj
        (verdierSpanFamilyDenominatorArrow i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z r.boundary.h) := by
  rw [r.cylinderSquare_terminal]
  simp only [squareColumnDiagram, ← Category.assoc, squareLeftEdge, lift_snd,
    Category.id_comp]

lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_family
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    parametricPullbackDiagramFamily r.cylinderSquare r.cylinderSquare_isPullback =
      r.cylinder.pullbacks := by
  have : Mono ((ihom (Δ[n] : SSet.{u})).map
      (fullSubcomplexOnVertices ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj B.obj)
        IsPullbackDiagramVertex).ι) := (ihom (Δ[n] : SSet.{u})).map_mono _
  apply (cancel_mono ((ihom (Δ[n] : SSet.{u})).map
    (fullSubcomplexOnVertices ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj B.obj)
      IsPullbackDiagramVertex).ι)).mp
  rw [parametricPullbackDiagramFamily_ι]
  exact pullbackFamilySquare_family r.cylinder.pullbacks

/-- 戻した同じ正方形の始域全族は、回収済み実余錐円柱の全前段そのもの。 -/
lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_prefix
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    pullbackSourcePrefixFamily
      (parametricPullbackDiagramFamily r.cylinderSquare r.cylinderSquare_isPullback) =
      r.cylinder.homotopy.h ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj := by
  rw [r.cylinderSquare_family]
  exact r.cylinder.homotopy_prefix.symm

/-- 別の補完を選ばず、同じ実円柱前段の全左辺が元の分母であることを証明する。 -/
lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_denominators
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f)
    (k : (Δ[n] : SSet.{u}) _⦋0⦌) (p : (S.toSSet ⊗ (Δ[1] : SSet.{u})) _⦋0⦌) :
    (squareLeftArrow (r.cylinderSquare ≫ evaluateFunctorAt k ≫ evaluateFunctorAt p)).edge ∈
      weakEquivalences i := by
  have hK := (isPullbackSquare_functor_iff r.cylinderSquare).mp r.cylinderSquare_isPullback k
  have hP := (isPullbackSquare_functor_iff (r.cylinderSquare ≫ evaluateFunctorAt k)).mp hK p
  have hK' := (isPullbackSquare_functor_iff r.square).mp r.square_pullback k
  have hP' := (isPullbackSquare_functor_iff (r.square ≫ evaluateFunctorAt k)).mp hK' p
  apply (weakEquivalences_pullback_iff h _ hP).mpr
  have hw := (weakEquivalences_pullback_iff h _ hP').mp (r.square_denominators k p)
  have hr : squareRightEdge ≫ (r.cylinderSquare ≫ evaluateFunctorAt k ≫ evaluateFunctorAt p) =
      squareRightEdge ≫ (r.square ≫ evaluateFunctorAt k ≫ evaluateFunctorAt p) := by
    simpa only [Category.assoc] using
      congrArg (fun f => f ≫ evaluateFunctorAt k ≫ evaluateFunctorAt p) r.cylinderSquare_right
  simpa only [squareRightArrow_edge, Category.assoc, hr] using hw

/-- 元の同じ実円柱前段の転置は、復元した正方形の始域頂点に厳密に一致する。 -/
lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_source
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    squareVertex r.cylinderSquare 0 0 = functorVertex
      (internalHomFlipHomEquiv (S.toSSet ⊗ (Δ[1] : SSet.{u})) Δ[n] B.obj
        (r.cylinder.homotopy.h ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj)) := by
  have hs := pullbackSourcePrefixFamily_parametric r.cylinderSquare r.cylinderSquare_isPullback
  rw [r.cylinderSquare_prefix] at hs
  have ht := congrArg (internalHomFlipHomEquiv (S.toSSet ⊗ (Δ[1] : SSet.{u})) Δ[n] B.obj) hs
  have hh := (internalHomFlipHomEquiv Δ[n] (S.toSSet ⊗ (Δ[1] : SSet.{u})) B.obj).symm_apply_apply
      ((functorVertexEquiv Δ[n] ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj B.obj)).symm
        (squareVertex r.cylinderSquare 0 0))
  have ht' : internalHomFlipHomEquiv (S.toSSet ⊗ (Δ[1] : SSet.{u})) Δ[n] B.obj
      (r.cylinder.homotopy.h ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj) =
      (functorVertexEquiv Δ[n] ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj B.obj)).symm
        (squareVertex r.cylinderSquare 0 0) := ht.trans hh
  exact ((congrArg functorVertex ht').trans
    ((functorVertexEquiv Δ[n] ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj B.obj)).apply_symm_apply
      _)).symm

/-- 同じ実左辺の商像自身が可逆であり、別の比較辺の存在で代用しない。 -/
lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_left_quotient_isInvertible
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    IsInvertibleEdge
      (X := (ihom (Δ[n] : SSet.{u})).obj
        ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj C.obj))
      ((squareLeftArrow r.cylinderSquare).map ((truncation 2).map
        ((ihom (Δ[n] : SSet.{u})).map
          ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map q.hom)))) :=
  verdierParametricSourceEdge_isInvertible h r.cylinderSquare r.cylinderSquare_denominators

/-- 可逆と証明した同じ実左辺の終端成分は、元の全分母経路の同じ商像。 -/
lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_left_quotient_terminal
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    (evaluateFunctorAt (Y := (ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj C.obj)
      (stdSimplex.obj₀Equiv.symm (Fin.last n))).app (Opposite.op ⦋1⦌)
      (((squareLeftArrow r.cylinderSquare).map ((truncation 2).map
        ((ihom (Δ[n] : SSet.{u})).map
          ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map q.hom)))).edge) =
      SSet.yonedaEquiv
        (internalHomFlipHomEquiv (S.toSSet ⊗ (Δ[1] : SSet.{u})) Δ[1] B.obj
          (verdierSpanFamilyDenominatorArrow i
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z r.boundary.h) ≫
          (ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map q.hom) := by
  have hn : (ihom (Δ[n] : SSet.{u})).map
        ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map q.hom) ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) ≫
        (ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map q.hom := rfl
  change ((ihom (Δ[n] : SSet.{u})).map
      ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map q.hom) ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n))).app (Opposite.op ⦋1⦌)
      (squareLeftArrow r.cylinderSquare).edge = _
  rw [hn, squareLeftArrow_edge, ← SSet.yonedaEquiv_comp]
  change SSet.yonedaEquiv (squareLeftEdge ≫ r.cylinderSquare ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) ≫
      (ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map q.hom) = _
  apply congrArg SSet.yonedaEquiv
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ (ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map q.hom)
    r.cylinderSquare_terminal_left

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.cylinderSquareFiniteLimits := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.cylinderSquareFiniteLimits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.cylinderSquareParameterFiniteLimits := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.cylinderSquareParameterFiniteLimits

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_denominators := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_denominators

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_end := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_end

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_family := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_family

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_isPullback := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_isPullback

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_left_quotient_isInvertible := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_left_quotient_isInvertible

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_left_quotient_terminal := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_left_quotient_terminal

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_original := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_original

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_prefix := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_prefix

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_right := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_source := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_start := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_start

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_terminal := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_terminal

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_terminal_left := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_terminal_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_top := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_top
