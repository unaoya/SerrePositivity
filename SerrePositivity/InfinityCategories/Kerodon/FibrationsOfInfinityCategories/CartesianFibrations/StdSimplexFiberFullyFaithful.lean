module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.StdSimplexTerminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.ThinNerveInnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteTotalFibers
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Edges

/-!
概要：標準単体上の頂点 fiber の包含の充満忠実性。
方針：頂点の包含の写像空間が一点であることを使い、充満忠実性を基底変換する。
規約：全空間は quasicategory、射影先は任意の標準単体。
使われ方：Kerodon Proposition 5.1.6.7（Tag 01VB）、区間上の同じ端点にある写像空間の比較。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：標準単体の各頂点の包含は充満忠実。
方針：零単体とその像の自己写像空間は各次数で一点なので誘導射は同型。
規約：頂点の包含の始域は標準零単体。
使われ方：Kerodon Proposition 5.1.6.7（Tag 01VB）、fiber の包含の基底変換表示。 -/
lemma stdSimplex_vertex_isFullyFaithful {n : ℕ} (b : (Δ[n] : SSet.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (SSet.const b : (Δ[0] : SSet.{u}) ⟶ Δ[n]) := by
  intro x y
  have hxy : x = y := by
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    have hx := (x i).isLt
    have hy := (y i).isLt
    omega
  subst y
  let v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x x) _⦋0⦌ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.vertexEquiv x x).symm (SSet.Truncated.Edge.id (X := (truncation 2).obj Δ[0]) x)
  let φ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (SSet.const b : (Δ[0] : SSet.{u}) ⟶ Δ[n]) x x
  have hφ : ∀ d, IsIso (φ.app d) := by
    rintro ⟨⟨m⟩⟩
    apply (isIso_iff_bijective _).mpr
    constructor
    · intro s t _
      exact Subsingleton.elim _ _
    · intro t
      exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v m, Subsingleton.elim _ _⟩
  have : IsIso φ := NatIso.isIso_of_isIso_app φ
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (asIso φ)).isQCatEquivalence.isSimplicialHomotopyEquivalence

/-- 概要：標準単体上の射の頂点 fiber の包含は充満忠実。
方針：標準単体の頂点包含を全空間へ基底変換し、fiber の標準同型で戻す。
規約：全空間は quasicategory、射影に追加の fibration 条件は不要。
使われ方：Kerodon Proposition 5.1.6.7（Tag 01VB）、同じ端点上の写像空間の比較。 -/
lemma vertexFiberι_stdSimplex_isFullyFaithful {E : SSet.{u}} [Quasicategory E]
    {n : ℕ} (p : E ⟶ (Δ[n] : SSet.{u})) (b : (Δ[n] : SSet.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) := by
  let j : (Δ[0] : SSet.{u}) ⟶ Δ[n] := SSet.const b
  have : InnerFibration j := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.stdSimplexTarget_innerFibration n j
  have : InnerFibration p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.stdSimplexTarget_innerFibration n p
  have : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiber_quasicategory_of_innerFibration p b
  have : InnerFibration (pullback.snd j p) :=
    ⟨innerFibrations.pullback_snd j p (InnerFibration.mem (q := j))⟩
  have : Quasicategory (pullback j p) := quasicategory_of_innerFibration (pullback.snd j p)
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ≅ pullback j p := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiber_isPullback p b).flip.isoPullback
  have he : e.hom ≫ pullback.snd j p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b :=
    IsPullback.isoPullback_hom_snd _
  rw [← he]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isFullyFaithful.comp
    ((stdSimplex_vertex_isFullyFaithful b).pullback_snd p)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
