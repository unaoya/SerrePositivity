module
public import SerrePositivity.KST.SConstruction.SurjectiveBaseChangeLifting
public import SerrePositivity.KST.SConstruction.ConnectedFibrationSurjectivity
public import SerrePositivity.KST.SConstruction.LocalizedTrivialFibrations
public import SerrePositivity.KST.Comparison.ArbitraryBasePullback
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationLocalizedLifting

/-! # 全単体全射な Kan 基底変換による局所化同型の検出
概要：全単体で全射な Kan fibration に沿う基底変換は Kan な標的への射の局所化同型を反映する。
方針：射を anodyne・Kan fibration に分解し、引き戻した右因子の境界 RLP を元へ戻す。
規約：標的の Kan 性を明示する。使われ方：連結基底上の面四角形の検出。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits HomotopicalAlgebra SSet
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open SerrePositivity.KST.Comparison
open scoped Simplicial

/-- 全単体全射な Kan fibration に沿う基底変換は Kan な標的への局所化同型を反映する。 -/
lemma localized_isIso_of_simplexSurjective_fibration_baseChange {E B : SSet.{u}}
    (t : E ⟶ B) (ht : J.rlp t)
    (hs : ∀ n : ℕ, Function.Surjective (t.app (Opposite.op ⦋n⦌)))
    {X Y : Over B} (f : X ⟶ Y) [KanComplex Y.left]
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map ((sliceFiberFunctor t).map f))) :
    IsIso (AnodyneHomotopy.anodyneQ.map f.left) := by
  let F := sliceFiberFunctor t
  let Q := AnodyneHomotopy.anodyneQ
  let d := AnodyneKanReplacement.factorization.factorizationData f.left
  let Z : Over B := Over.mk (d.p ≫ Y.hom)
  let j : X ⟶ Z := Over.homMk d.i (by
    change d.i ≫ (d.p ≫ Y.hom) = X.hom
    rw [← Category.assoc, d.fac, Over.w f])
  let k : Z ⟶ Y := Over.homMk d.p
  have hjk : j ≫ k = f := by
    apply Over.OverMorphism.ext
    exact d.fac
  have hj : IsIso (Q.map (F.map j)) :=
    sliceFiberFunctor_localized_isIso_anyBase t ht j
      ((Localization.inverts Q anodyneExtensions) d.i d.hi)
  have hk : IsIso (Q.map (F.map k)) := by
    have hc : Q.map (F.map j) ≫ Q.map (F.map k) = Q.map (F.map f) := by
      rw [← Q.map_comp, ← F.map_comp, hjk]
    have hic : IsIso (Q.map (F.map j) ≫ Q.map (F.map k)) := hc.symm ▸ hf
    exact (isIso_comp_left_iff _ _).mp hic
  have hkr : J.rlp (F.map k) :=
    J.rlp.of_isPullback (sliceFiberFunctor_map_isPullback t k).flip d.hp
  let : Fibration t := (SSet.modelCategoryQuillen.fibration_iff _).mpr ht
  let : Fibration (pullback.fst Y.hom t) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mpr (J.rlp.pullback_fst Y.hom t ht)
  let : KanComplex ((sliceFiberFunctor t).obj Y) :=
    isFibrant_of_fibration (pullback.fst Y.hom t)
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (F.map k) := ⟨KanFibrationLocalizedLifting.of_localized_isIso
    (F.map k) hkr ((SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance) hk⟩
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration k.left :=
    trivialKanFibration_of_simplexSurjective_baseChange t hs k
  have hjl : IsIso (Q.map j.left) := (Localization.inverts Q anodyneExtensions) d.i d.hi
  have hkl : IsIso (Q.map k.left) := map_isIso_of_trivialKanFibration Q
    (Localization.inverts Q anodyneExtensions) k.left
  have hfac : j.left ≫ k.left = f.left := d.fac
  rw [← hfac, Q.map_comp]
  infer_instance

/-- 連結な Kan 基底の非空な Kan fibration に沿う基底変換は局所化同型を反映する。 -/
lemma localized_isIso_of_connected_fibration_baseChange {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] [SSet.IsPreconnected B]
    (t : E ⟶ B) [Fibration t] (e : E _⦋0⦌)
    {X Y : Over B} (f : X ⟶ Y) [KanComplex Y.left]
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map ((sliceFiberFunctor t).map f))) :
    IsIso (AnodyneHomotopy.anodyneQ.map f.left) :=
  localized_isIso_of_simplexSurjective_fibration_baseChange t
    ((SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance)
    (fibration_simplex_surjective_of_connected t e) f hf

end SerrePositivity.KST.SConstruction
