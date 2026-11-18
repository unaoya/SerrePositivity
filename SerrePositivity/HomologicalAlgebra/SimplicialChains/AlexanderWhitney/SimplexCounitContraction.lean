module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainCounit
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexAugmentationZero

/-!
# 標準単体の AW 余単位の収縮

概要：既存 AW 余単位自身の鎖ホモトピー同値性を証明する。
方針：零次生成元の値で既存の正規化単体収縮の順射と照合する。
規約：任意可換環上の同じ複体・同じ余単位を保持する。
使われ方：Sp の β6 f4b の標準単体の余単位。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.SimplicialChains.AlexanderWhitney
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.AlgebraicTopology _root_.AlgebraicTopology.DoldKan
open _root_.SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.ComplexLimits
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- 概要：鎖 AW 余単位と既存の単体収縮の順射の一致。
方針：single₀ への射を零次数の正規化生成元で照合する。
規約：同じ標準単体・単位複体。使われ方：整数コチェインへの延長。 -/
lemma counit_stdSimplex_eq_contraction (n : SimplexCategory) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.counit A (SSet.stdSimplex.obj n) = (_root_.SerrePositivity.ComplexLimits.normalizedSimplexChainContraction A n).hom := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  change (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.counit A (SSet.stdSimplex.obj n)).f 0 = _
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.counit_f_zero]
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_hom_ext A (SSet.stdSimplex.obj n) 0
  intro x
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.vertexAugmentation_generator]
  have hp : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization A (SSet.stdSimplex.obj n)).f 0 ≫
      (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj n))).hom =
      𝟙 _ := by
    change ((PInftyToNormalizedMooreComplex _ ≫ inclusionOfMooreComplexMap _).f 0) = _
    rw [PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap]
    rfl
  have hg : _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (SSet.stdSimplex.obj n) 0 x =
      (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj n))).inv
        (ModuleCat.freeMk (ULift.up x)) := by
    have h : (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalization A (SSet.stdSimplex.obj n)).f 0 =
        (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj n))).inv := by
      apply (cancel_mono (_root_.SerrePositivity.ComplexLimits.mooreDegreeZeroIso
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj (SSet.stdSimplex.obj n))).hom).mp
      rw [hp, Iso.inv_hom_id]
    exact ConcreteCategory.congr_hom h (ModuleCat.freeMk (ULift.up x))
  rw [hg]
  exact (_root_.SerrePositivity.ComplexLimits.normalizedSimplexChainAugmentation_zero A n x).symm

/-- 概要：整数 AW 余単位と既存の単体収縮の順射の一致。
方針：鎖の等式を同じ負次数延長と単位の比較へ送る。
規約：射自身の等式。使われ方：余単位自身のホモトピー同値性。 -/
lemma cochainCounit_stdSimplex_eq_contraction (n : SimplexCategory) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n) = (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).hom := by
  change extendMap (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.counit A (SSet.stdSimplex.obj n)) ComplexShape.embeddingDownNat ≫ _ = _
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.counit_stdSimplex_eq_contraction]
  rfl

/-- 概要：元の AW 余単位を順射とする実鎖ホモトピー同値。
方針：既存の収縮を元の余単位の等式で書き換える。
規約：逆射・両ホモトピーもデータとして保持。
使われ方：Sp の標準単体の収縮。 -/
def cochainCounitStdSimplexHomotopyEquiv (n : SimplexCategory) :
    HomotopyEquiv (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A (SSet.stdSimplex.obj n)) (𝟙_ (Complex A)) :=
  (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainContraction A n).copy
    (Homotopy.ofEq (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_stdSimplex_eq_contraction A n).symm)

/-- 概要：束ねたホモトピー同値の順射は元の AW 余単位。
方針：copy の定義を読む。規約：定義上の一致。使われ方：元の射の回収。 -/
@[simp] lemma cochainCounitStdSimplexHomotopyEquiv_hom (n : SimplexCategory) :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounitStdSimplexHomotopyEquiv A n).hom = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n) := rfl

/-- 概要：標準単体の元の AW 余単位自身は鎖ホモトピー同値。
方針：実収縮のデータを存在命題へ渡す。規約：追加の instance 仮定なし。
使われ方：Sp の β6 f4b の弱同値判定。 -/
lemma cochainCounit_stdSimplex_homotopyEquivalence (n : SimplexCategory) :
    HomologicalComplex.homotopyEquivalences (ModuleCat A) (.up ℤ)
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n)) :=
  ⟨_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounitStdSimplexHomotopyEquiv A n, rfl⟩

private lemma chains_point_isZero (k : ℕ) (hk : k ≠ 0) :
    IsZero ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (SSet.stdSimplex.obj ⦋0⦌)).X k) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_hom_ext A (SSet.stdSimplex.obj ⦋0⦌) k
  intro x
  let θ : ⦋k⦌ ⟶ ⦋0⦌ := SimplexCategory.const _ _ 0
  have hθ : ¬ Mono θ := by
    intro h
    have h' := (SimplexCategory.mono_iff_injective).mp h
    change Function.Injective (fun _ : Fin (k + 1) => (0 : Fin 1)) at h'
    have he := h' (a₁ := ⟨0, by omega⟩) (a₂ := ⟨1, by omega⟩) (Subsingleton.elim _ _)
    exact Nat.zero_ne_one (congrArg Fin.val he)
  let y : (SSet.stdSimplex.obj ⦋0⦌ : SSet.{0}) _⦋0⦌ :=
    SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)
  have hx : (SSet.stdSimplex.obj ⦋0⦌).map θ.op y = x := by
    apply SSet.stdSimplex.objEquiv.injective
    exact Subsingleton.elim _ _
  change _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A (SSet.stdSimplex.obj ⦋0⦌) k x = 0
  simpa only [hx] using
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_map_of_not_mono A (SSet.stdSimplex.obj ⦋0⦌) k θ hθ y

private lemma chainContraction_point_isIso :
    IsIso (_root_.SerrePositivity.ComplexLimits.normalizedSimplexChainContraction A ⦋0⦌).hom := by
  have strict : ∀ {K : ChainComplex (ModuleCat A) ℕ},
      (∀ k : ℕ, k ≠ 0 → IsZero (K.X k)) →
      ∀ {f g : K ⟶ K}, Homotopy f g → f = g := by
    intro K hz f g h
    apply HomologicalComplex.hom_ext
    intro k
    by_cases hk : k = 0
    · subst k
      have hh : h.hom 0 1 = 0 := (hz 1 (by decide)).eq_of_tgt _ _
      have hc := h.comm 0
      rw [dNext_eq_zero _ 0 (by decide), prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 from rfl),
        hh, zero_comp, zero_add, zero_add] at hc
      exact hc
    · exact (hz k hk).eq_of_src _ _
  let e := _root_.SerrePositivity.ComplexLimits.normalizedSimplexChainContraction A ⦋0⦌
  exact ⟨⟨e.inv, strict (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains_point_isZero A) e.homotopyHomInvId,
    strict (fun k hk => isZero_single_obj_X (.down ℕ) 0 (𝟙_ (ModuleCat A)) k hk)
      e.homotopyInvHomId⟩⟩

/-- 概要：零単体の AW 余単位は複体の同型。
方針：正次数の正規化鎖が零なので収縮の両ホモトピーを等式に強め、延長する。
規約：元の余単位自身の IsIso。大域 instance は追加しない。
使われ方：Sp の β6 f4b の零単体条件。 -/
lemma cochainCounit_stdSimplexZero_isIso :
    IsIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj ⦋0⦌)) := by
  have := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chainContraction_point_isIso A
  have : IsIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.counit A (SSet.stdSimplex.obj ⦋0⦌)) := by
    rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.counit_stdSimplex_eq_contraction]
    infer_instance
  unfold _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit
  change IsIso ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).map
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.counit A (SSet.stdSimplex.obj ⦋0⦌)) ≫ _)
  infer_instance

end SerrePositivity.SimplicialChains.AlexanderWhitney
