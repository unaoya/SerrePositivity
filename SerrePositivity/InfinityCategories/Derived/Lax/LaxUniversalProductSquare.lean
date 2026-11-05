module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

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
namespace SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct
open SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct
local instance instSimplicialCategoryOmegaSpectrum : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {Φ : StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

def cornerIso (a b : Fin 2) : Σ x : Sp.{u} _⦋0⦌,
    VertexIso (squareVertex (LaxUniversalValue.square Φ p q i r h) a b) x := by
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
    VertexIso ((LaxUniversalValue.square Φ p q i r h).app (Opposite.op ⦋0⦌) v) x := by
  let a := stdSimplex.obj₀Equiv v.1
  let b := stdSimplex.obj₀Equiv v.2
  have he : (LaxUniversalValue.square Φ p q i r h).app (Opposite.op ⦋0⦌) v =
      squareVertex (LaxUniversalValue.square Φ p q i r h) a b := by
    change _ = (LaxUniversalValue.square Φ p q i r h).app _
      (stdSimplex.obj₀Equiv.symm (stdSimplex.obj₀Equiv v.1),
        stdSimplex.obj₀Equiv.symm (stdSimplex.obj₀Equiv v.2))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  exact ⟨(cornerIso hΦ p q i r h a b).1,
    eqToIso (congrArg HomotopyCategory.mk he) ≪≫ (cornerIso hΦ p q i r h a b).2⟩

def vertexPaths : DiagramVertexPaths (LaxUniversalValue.square Φ p q i r h) :=
  DiagramVertexPaths.ofIso (vertexIsos hΦ p q i r h)

def extension : (vertexPaths hΦ p q i r h).Extension := (vertexPaths hΦ p q i r h).extension

def square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} := (extension hΦ p q i r h).target

def comparison : FunctorIso (LaxUniversalValue.square Φ p q i r h) (square hΦ p q i r h) :=
  (extension hΦ p q i r h).comparison

lemma square_isPullback : IsPullbackSquare (square hΦ p q i r h) :=
  (extension hΦ p q i r h).target_isPullback
    (LaxUniversalDifference.comparisonSquare_value_isPullback p q i r h hΦ)

end SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.comparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.comparison := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.comparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.cornerIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.cornerIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.extension (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.extension := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.extension

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.instSimplicialCategoryOmegaSpectrum (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.instSimplicialCategoryOmegaSpectrum := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.instSimplicialCategoryOmegaSpectrum

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.square (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.square := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.square

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.square_isPullback := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.square_isPullback

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.vertexIsos (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.vertexIsos := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.vertexIsos

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.vertexPaths (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.vertexPaths := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.vertexPaths

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.cornerIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.cornerIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.cornerIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.cornerIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso._proof_5 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.cornerIso._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso._proof_6 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.cornerIso._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso._proof_7 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.cornerIso._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso._proof_8 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.cornerIso._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.cornerIso._proof_9 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.cornerIso._proof_9

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.vertexIsos._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.vertexIsos._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.LaxUniversalProduct.vertexIsos._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.LaxUniversalProduct.vertexIsos._proof_2
