module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuNullTriangleFactor

/-!
概要：指定商比較の全パラメータを、同じ核包含との合成で零 Hom に置く。
方針：元の豊穣 Hom の前合成を使い、元の比較辺とその全単体を保持する。
規約：商境界の指定比較を選び直さない。使われ方：実面比較の混合三角形。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
private lemma projectionNullEdgeSource {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) :
    (SSet.yonedaEquiv.symm e.edge).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = x := by
  have hz : stdSimplex.objEquiv (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      SimplexCategory.δ (1 : Fin 2) := by
    ext a
    fin_cases a
    rfl
  rw [SSet.yonedaEquiv_symm_app, hz]
  exact e.src_eq

private lemma projectionNullEdgeTarget {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) :
    (SSet.yonedaEquiv.symm e.edge).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = y := by
  have hz : stdSimplex.objEquiv (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      SimplexCategory.δ (0 : Fin 2) := by
    ext a
    fin_cases a
    rfl
  rw [SSet.yonedaEquiv_symm_app, hz]
  exact e.tgt_eq

private lemma projectionNullWhiskerVertex {X Y Z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors X Z : SSet.{u})).ι.app (Opposite.op ⦋0⦌)
      ((eHomWhiskerRight (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) SSet f Z).app (Opposite.op ⦋0⦌)
        (SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) Y Z g)) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv X Z (f ≫ g) := by
  rfl

variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
local notation "K" => dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)
local notation "A" => dgKInputStableValue R (dgOdotMilnorCellInput R d)
local notation "B" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "i" => dgOdotMilnorFlatKernelExactMap R d
local notation "e" => dgOdotMilnorNuProjectionCoreEdge R d h

/-- 概要：指定商比較の同じ全一単体を元核包含で前合成する。
方針：豊穣 Hom の通常の前合成作用を使う。
規約：元比較辺をそのまま使う。使われ方：混合面の零合成パラメータ。 -/
def dgOdotMilnorNuProjectionNullHom : (Δ[1] : SSet.{u + 1}) ⟶
    SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (K) (B) :=
  SSet.yonedaEquiv.symm (e).edge ≫ eHomWhiskerRight (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) SSet (i) (B)

/-- 概要：指定商比較の元零端点は同じ実包含・商合成の関手頂点。
方針：元辺の始点式と豊穣前合成の単位評価を使う。
規約：固定 ν の元実合成。使われ方：全比較像の零成分判定。 -/
lemma dgOdotMilnorNuProjectionNullHom_source :
    (dgOdotMilnorNuProjectionNullHom R d h ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (K) (B) : SSet.{u + 1})).ι).app
        (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv (K) (B) (dgOdotMilnorNuNullComposite R d) := by
  have hs : (SSet.yonedaEquiv.symm (e).edge).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      SimplicialCategory.homEquiv' (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) (A) (B)
        (dgOdotMilnorCellProjectionExactMap R d) := projectionNullEdgeSource (e)
  have hv := congrArg (fun x =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (K) (B) : SSet.{u + 1})).ι.app (Opposite.op ⦋0⦌)
      ((eHomWhiskerRight (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) SSet (i) (B)).app
        (Opposite.op ⦋0⦌) x)) hs
  exact hv.trans (projectionNullWhiskerVertex
    (i) (dgOdotMilnorCellProjectionExactMap R d))

/-- 概要：同じ核包含と同じ完備化後射影の実完全合成。
方針：元の二射の基礎写像を合成する。
規約：固定 ν の両端点。使われ方：指定商比較の終点。 -/
def dgOdotMilnorNuProjectionNullTargetComposite : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (K) (B) where
  hom := (i).hom ≫ (dgOdotMilnorNuPerfectSequence R d h).projection.hom
  isExact := @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isExactFunctor_comp _ _ _ _ _ (i).isExact
    (dgOdotMilnorNuPerfectSequence R d h).projection.isExact

/-- 概要：指定商比較の元一端点は同じ完備化後射影との実合成。
方針：同じ辺の終点式と元の豊穣前合成の頂点評価を使う。
規約：同じ指定商比較。使われ方：全パラメータの零成分への制限。 -/
lemma dgOdotMilnorNuProjectionNullHom_target :
    (dgOdotMilnorNuProjectionNullHom R d h ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (K) (B) : SSet.{u + 1})).ι).app
        (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv (K) (B)
        (dgOdotMilnorNuProjectionNullTargetComposite R d h) := by
  have hs := projectionNullEdgeTarget (e)
  have hv := congrArg (fun x =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (K) (B) : SSet.{u + 1})).ι.app (Opposite.op ⦋0⦌)
      ((eHomWhiskerRight (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1}) SSet (i) (B)).app
        (Opposite.op ⦋0⦌) x)) hs
  exact hv.trans (projectionNullWhiskerVertex
    (i) (dgOdotMilnorNuPerfectSequence R d h).projection)

/-- 概要：同じ商比較を前合成した全 Hom の全頂点は終関手。
方針：元の二端点で実商列の全零性を点ごとの終対象性へ移す。
規約：比較辺の全像を保持。使われ方：指定混合面の全零性。 -/
lemma dgOdotMilnorNuProjectionNullHom_vertex_isTerminal
    (a : (Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((dgOdotMilnorNuProjectionNullHom R d h ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (K) (B) : SSet.{u + 1})).ι).app
        (Opposite.op ⦋0⦌) a) := by
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv (K) (B) (dgOdotMilnorNuNullComposite R d)) := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _).reflects_isTerminalVertex
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgOdotMilnorNuNullComposite R d).hom)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise _
      (fun x => (dgOdotMilnorNuNullComposite_zero R d h x).2)
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctorVertexEquiv (K) (B)
      (dgOdotMilnorNuProjectionNullTargetComposite R d h)) := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _).reflects_isTerminalVertex
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      ((i).hom ≫ (dgOdotMilnorNuPerfectSequence R d h).projection.hom))
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_functorVertex_of_pointwise _
      (fun x => ((dgOdotMilnorNuPerfectSequence R d h).projection_kills_inclusion x).2)
  have hp₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((dgOdotMilnorNuProjectionNullHom R d h ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (K) (B) : SSet.{u + 1})).ι).app
        (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) :=
    (dgOdotMilnorNuProjectionNullHom_source R d h).symm ▸ h₀
  have hp₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((dgOdotMilnorNuProjectionNullHom R d h ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (K) (B) : SSet.{u + 1})).ι).app
        (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :=
    (dgOdotMilnorNuProjectionNullHom_target R d h).symm ▸ h₁
  have hx (k : Fin 2) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex ((dgOdotMilnorNuProjectionNullHom R d h ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (K) (B) : SSet.{u + 1})).ι).app
        (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm k)) := by
    fin_cases k
    · exact hp₀
    · exact hp₁
  exact (stdSimplex.obj₀Equiv.symm_apply_apply a) ▸ hx (stdSimplex.obj₀Equiv a)

/-- 概要：指定商比較の全パラメータを同じ固定 ν の零合成空間へ置く。
方針：全頂点の終関手性で元の全 Hom 写像を制限する。
規約：元商比較の全単体を保持。使われ方：混合比較面の相対充填。 -/
def dgOdotMilnorNuProjectionNullFactor :
    (Δ[1] : SSet.{u + 1}) ⟶ DGOdotMilnorNuNullCoherenceSpace R d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (dgOdotMilnorNuProjectionNullHom R d h ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (K) (B) : SSet.{u + 1})).ι)
    (dgOdotMilnorNuProjectionNullHom_vertex_isTerminal R d h)

/-- 概要：混合面の零因子分解は同じ指定商比較の前合成を厳密に回収する。
方針：元の core 包含の単射性で持ち上げの包含式を戻す。
規約：全単体の等号。使われ方：指定境界を保つ全図式比較。 -/
lemma dgOdotMilnorNuProjectionNullFactor_hom :
    dgOdotMilnorNuProjectionNullFactor R d h ≫ dgOdotMilnorNuNullCoherenceHom R d h =
      dgOdotMilnorNuProjectionNullHom R d h := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors (K) (B) : SSet.{u + 1})).ι).mp
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f => dgOdotMilnorNuProjectionNullFactor R d h ≫ f)
      (dgOdotMilnorNuNullCoherenceHom_inclusion R d h))

end SerrePositivity.KST.SConstruction
