module

public import SerrePositivity.KST.Comparison.FreeStandardZeroVertex
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ExtraDegeneracyContraction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveStandard

/-!
# 標準単体の自由な退化の実際の収縮

概要：零点追加の余分な退化を構成し、標準単体上の augmentation の局所化可逆性を示す。
方針：全次数の面・退化の恒等式を、標準形の計算から証明した写像へ適用する。
規約：Segal 1974 Proposition 1.6 の模型比較のための独自の自由な退化の経路。
収縮は既存の ExtraDegeneracyContraction の実際の区間ホモトピーによる。
使われ方：セルによる一般の単体集合への augmentation の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite
open scoped _root_.Simplicial
open SerrePositivity.SimplicialModel

/--
概要：自由な退化の標準単体を一点へ増大した単体対象。
方針：augmentation を各次数の一点への一意な写像とする。
規約：右辺の一点は値宇宙の PUnit。
使われ方：余分な退化から収縮を得る入力。
-/
def freeStandardAugmented (n : ℕ) : SimplicialObject.Augmented (Type u) where
  left := freeDegeneracies.obj (Δ[n] : SSet.{u})
  right := PUnit.{u + 1}
  hom := { app _ := ↾fun _ => PUnit.unit }

/--
概要：自由な退化の標準単体への零点追加は実際の余分な退化を定める。
方針：最初の面と第零次数の計算、拡張した単体作用との交換を使う。
規約：通常の面・退化との全ての恒等式を証明する。
使われ方：標準単体上の区間ホモトピーによる収縮。
-/
def freeStandardExtraDegeneracy (k : ℕ) :
    SimplicialObject.Augmented.ExtraDegeneracy (freeStandardAugmented.{u} k) where
  s' := ↾fun _ => freeStandardZeroVertex k
  s n := freeStandardPrepend k n
  s'_comp_ε := by
    apply ConcreteCategory.hom_ext
    intro x
    change (PUnit.unit : PUnit.{u + 1}) = x
    exact Subsingleton.elim _ _
  s₀_comp_δ₁ := by
    apply ConcreteCategory.hom_ext
    intro x
    apply (freeDegeneraciesNormalForm (Δ[k] : SSet.{u}) (op ⦋0⦌)).injective
    change freeDegeneraciesNormalForm (Δ[k] : SSet.{u}) (op ⦋0⦌)
      ((freeDegeneracies.obj (Δ[k] : SSet.{u})).map (SimplexCategory.δ 1).op
        (fatNormalFormRealize _ _ (freeStandardPrependNormalForm
          (freeDegeneraciesNormalForm _ _ x)))) =
      fatDegreeNormalize (discreteRowsFunctor.obj (Δ[k] : SSet.{u})) (op ⦋0⦌)
        (fatNormalFormRealize _ _ (freeStandardZeroNormalForm k))
    rw [freeStandardPrependNormalForm_δ_one, fatDegreeNormalize_realize]
  s_comp_δ₀ n := freeStandardPrepend_δ_zero k n
  s_comp_δ n i := by
    change freeStandardPrepend k (n + 1) ≫
      (freeDegeneracies.obj (Δ[k] : SSet.{u})).map (SimplexCategory.δ i.succ).op =
      (freeDegeneracies.obj (Δ[k] : SSet.{u})).map (SimplexCategory.δ i).op ≫
        freeStandardPrepend k n
    have h := freeStandardPrepend_naturality.{u} (n := k) (SimplexCategory.δ i)
    rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_δ] at h
    exact h
  s_comp_σ n i := by
    change freeStandardPrepend k n ≫
      (freeDegeneracies.obj (Δ[k] : SSet.{u})).map (SimplexCategory.σ i.succ).op =
      (freeDegeneracies.obj (Δ[k] : SSet.{u})).map (SimplexCategory.σ i).op ≫
        freeStandardPrepend k (n + 1)
    have h := freeStandardPrepend_naturality.{u} (n := k) (SimplexCategory.σ i)
    rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend_σ] at h
    exact h

/--
概要：自由な退化の標準単体から一点への写像は局所化同型である。
方針：実際の余分な退化の区間ホモトピーによる収縮を使う。
規約：可縮性を仮定として置かない。
使われ方：標準単体上の元への augmentation の比較。
-/
theorem freeStandardAugmented_localized_isIso (n : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (freeStandardAugmented.{u} n).hom) :=
  ExtraDegeneracyContraction.localized_augmentation_isIso (freeStandardExtraDegeneracy n)

/--
概要：自由な退化から元への augmentation は標準単体上で局所化同型である。
方針：両方の一点への写像の局所化可逆性と、その合成の一意性を使う。
規約：全ての標準単体と値宇宙で成り立つ。
使われ方：セルによる任意の単体集合への比較。
-/
theorem freeDegeneraciesAugmentation_standard_localized_isIso (n : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (freeDegeneraciesAugmentation.app (Δ[n] : SSet.{u}))) := by
  let hpoint := Functor.isTerminalConst SimplexCategoryᵒᵖ Types.isTerminalPUnit.{u}
  let e := SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso hpoint
  let p : (Δ[n] : SSet.{u}) ⟶ (SimplicialObject.const (Type u)).obj PUnit.{u + 1} :=
    SSet.stdSimplex.isTerminalObj₀.from _ ≫ e.hom
  have hp : IsIso (AnodyneHomotopy.anodyneQ.map p) := by
    have h := SimplexNerve.standardTerminal_isIso AnodyneHomotopy.anodyneQ
      (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions) n
    dsimp only [p]
    rw [Functor.map_comp]
    infer_instance
  have he : freeDegeneraciesAugmentation.app (Δ[n] : SSet.{u}) ≫ p =
      (freeStandardAugmented n).hom := hpoint.hom_ext _ _
  have hc : IsIso (AnodyneHomotopy.anodyneQ.map
      (freeDegeneraciesAugmentation.app (Δ[n] : SSet.{u})) ≫ AnodyneHomotopy.anodyneQ.map p) := by
    rw [← Functor.map_comp, he]
    exact freeStandardAugmented_localized_isIso n
  exact (isIso_comp_right_iff _ _).mp hc

end SerrePositivity.KST.Comparison
