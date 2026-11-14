module
public import SerrePositivity.KST.SConstruction.ZeroCofiberFunctors

/-! # 標準零 cofiber 関手の完全性
概要：McCarthy の λ と ι の標準 cofiber 関手は零対象と全押し出しを保つ。
方針：入力の両端は恒等または零関手であり、cofiber 射影で普遍性を反映する。
規約：元の標準正方形の族を使う。使われ方：gapped 図式への後合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：指定零対象への定値関手は零対象と全押し出しを保つ。
方針：定値正方形は退化した押し出し。
規約：源は任意、標的は quasicategory。使われ方：零 cofiber 関手の完全性。 -/
lemma constantZero_preservesSConstructionData {A C : SSet.{u}} [Quasicategory C]
    (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) : PreservesSConstructionData (SSet.const z.vertex : A ⟶ C) := by
  constructor
  · intro a _
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z.vertex 0)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact z.isZero
  · intro F _
    rw [SSet.comp_const]
    have h := identityPushoutShape_isPushout false
      (SSet.const z.vertex : (Δ[1] : SSet.{u}) ⟶ C)
    rwa [SSet.comp_const] at h

/-- 概要：関手圏への射の完全性は各点での保存から得られる。
方針：零対象と全押し出しの点ごとの判定。
規約：C は安定な quasicategory、パラメーターと源は任意。使われ方：標準入力の完全性。 -/
lemma preservesSConstructionData_functor_of_pointwise {A K C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (f : A ⟶ (ihom K).obj C)
    (hf : ∀ k : K _⦋0⦌, PreservesSConstructionData (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)) :
    PreservesSConstructionData f := by
  constructor
  · intro a ha
    exact isZeroVertex_of_pointwise _ (fun k => (hf k).1 a ha)
  · intro F hF
    apply (functor_pushout_iff_pointwise _).2
    intro k
    simpa only [Category.assoc] using (hf k).2 F hF

/-- 概要：自明ファイブレーションとの合成の完全性から元の射の完全性を得る。
方針：各零頂点と各正方形の普遍性を反映する。
規約：安定性は不要。使われ方：cofiber 関手の入力での判定。 -/
lemma preservesSConstructionData_of_comp_trivialKanFibration {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    (f : A ⟶ E) (hf : PreservesSConstructionData (f ≫ p)) :
    PreservesSConstructionData f := by
  constructor
  · intro a ha
    exact (isZeroVertex_iff_of_trivialKanFibration p _).2 (hf.1 a ha)
  · intro F hF
    apply (isPushoutSquare_iff_postcomp_of_trivialKanFibration p _).2
    simpa only [Category.assoc] using hf.2 F hF

/-- 概要：二つの標準零 cofiber 関手は零対象と全押し出しを保つ。
方針：入力の各端点での完全性を確認し、自明ファイブレーションで反映する。
規約：C は安定な quasicategory。使われ方：McCarthy の λ と ι を gapped 図式に適用する。 -/
lemma zeroCofiberFunctor_preservesSConstructionData {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex C) (b : Bool) :
    PreservesSConstructionData (zeroCofiberFunctor z b) := by
  apply preservesSConstructionData_of_comp_trivialKanFibration (cofiberProjection C)
  apply preservesSConstructionData_functor_of_pointwise
  intro k
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective k
  rw [Category.assoc, zeroCofiberFunctor_input_evaluation]
  split_ifs
  · exact constantZero_preservesSConstructionData z
  · exact preservesSConstructionData_id C

end SerrePositivity.KST.SConstruction
