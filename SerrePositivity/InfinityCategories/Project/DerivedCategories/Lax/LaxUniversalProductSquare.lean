module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.LaxUniversalValueVertices
public import SerrePositivity.KST.LocalizingInvariants.DiagramVertexTransport

/-!
概要：普遍差の比較の実 pullback 正方形を、元の二つの BF 積を頂点に持つ正方形へ移す。
方針：元の Tamme 射影同値を頂点で指定し、全図式の可逆 path を延長する。
規約：同じ E(A) と E(Q) を保持。辺の正規化は後続。使われ方：元の二脚の切除。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct
end SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct
local instance instSimplicialCategoryOmegaSpectrum : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)

def cornerIso (a b : Fin 2) : Σ x : Sp.{u} _⦋0⦌,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (LaxUniversalValue.square Φ p q i r h) a b) x := by
  refine Fin.cases ?_ (fun a => ?_) a
  · refine Fin.cases ?_ (fun b => ?_) b
    · exact ⟨_, eqToIso (congrArg HomotopyCategory.mk
        (LaxUniversalValue.vertex00 Φ p q i r h))⟩
    · have hb : b = 0 := by apply Fin.ext; omega
      subst b
      exact ⟨_, eqToIso (congrArg HomotopyCategory.mk
        (LaxUniversalValue.vertex01 Φ p q i r h))⟩
  · have ha : a = 0 := by apply Fin.ext; omega
    subst a
    refine Fin.cases ?_ (fun b => ?_) b
    · exact ⟨_, eqToIso (congrArg HomotopyCategory.mk
        (LaxUniversalValue.vertex10 Φ p q i r h)) ≪≫ hΦ.tammeProjectionEquivalence p q⟩
    · have hb : b = 0 := by apply Fin.ext; omega
      subst b
      exact ⟨_, eqToIso (congrArg HomotopyCategory.mk
        (LaxUniversalValue.vertex11 Φ p q i r h)) ≪≫
          hΦ.tammeProjectionEquivalence (𝟙 Q) (𝟙 Q)⟩

def vertexIsos (v : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) _⦋0⦌) : Σ x : Sp.{u} _⦋0⦌,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((LaxUniversalValue.square Φ p q i r h).app (Opposite.op ⦋0⦌) v) x := by
  let a := stdSimplex.obj₀Equiv v.1
  let b := stdSimplex.obj₀Equiv v.2
  have he : (LaxUniversalValue.square Φ p q i r h).app (Opposite.op ⦋0⦌) v =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (LaxUniversalValue.square Φ p q i r h) a b := by
    change _ = (LaxUniversalValue.square Φ p q i r h).app _
      (stdSimplex.obj₀Equiv.symm (stdSimplex.obj₀Equiv v.1),
        stdSimplex.obj₀Equiv.symm (stdSimplex.obj₀Equiv v.2))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  exact ⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.cornerIso hΦ p q i r h a b).1,
    eqToIso (congrArg HomotopyCategory.mk he) ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.cornerIso hΦ p q i r h a b).2⟩

def vertexPaths : DiagramVertexPaths (LaxUniversalValue.square Φ p q i r h) :=
  DiagramVertexPaths.ofIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.vertexIsos hΦ p q i r h)

def extension : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.vertexPaths hΦ p q i r h).Extension := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.vertexPaths hΦ p q i r h).extension

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.extension hΦ p q i r h).target

def comparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (LaxUniversalValue.square Φ p q i r h) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.extension hΦ p q i r h).comparison

lemma square_isPullback : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square hΦ p q i r h) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.extension hΦ p q i r h).target_isPullback
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.comparisonSquare_value_isPullback p q i r h hΦ)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.comparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.comparison := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.comparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.cornerIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.cornerIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.extension (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.extension := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.extension

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.instSimplicialCategoryOmegaSpectrum (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.instSimplicialCategoryOmegaSpectrum := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.instSimplicialCategoryOmegaSpectrum

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.square := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.square_isPullback := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.square_isPullback

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.vertexIsos (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.vertexIsos := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.vertexIsos

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.vertexPaths (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.vertexPaths := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.vertexPaths

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.cornerIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.cornerIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.cornerIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.cornerIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.cornerIso._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso._proof_6 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.cornerIso._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso._proof_7 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.cornerIso._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso._proof_8 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.cornerIso._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso._proof_9 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.cornerIso._proof_9

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.vertexIsos._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.vertexIsos._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.vertexIsos._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxUniversalProductSquare.vertexIsos._proof_2
