module
public import SerrePositivity.KST.Fibration.WeakStringVertices
public import SerrePositivity.KST.Fibration.WeakStringCofiberRealization
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # 有限 W 列と初期頂点・全連続 cofiber の積との比較

元の全有限列の反復実現から、初期頂点と全ての連続する辺の cofiber への射を束ねる。
空列を含み、各射影は元の評価を回収する。同値性は別に証明する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 標準単体の元の i 番目の連続辺。 -/
def consecutiveWeakStringEdge (n : ℕ) (i : Fin n) : ⦋1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk {
    toFun := fun j => ⟨i.val + j.val, by
      change i.val + j.val < n + 1
      have := i.isLt
      have hj : j.val < 2 := j.isLt
      omega⟩
    monotone' := fun _ _ h => Nat.add_le_add_left h _ }

/-- 一辺の列の元の唯一の連続辺は恒等射。 -/
lemma consecutiveWeakStringEdge_one (i : Fin 1) :
    consecutiveWeakStringEdge 1 i = 𝟙 ⦋1⦌ := by
  have hi : i = 0 := Fin.eq_zero i
  subst i
  ext j
  change 0 + j.val = j.val
  omega

/-- 全連続辺の元の cofiber 実現射を有限積に束ねる。 -/
def weakStringConsecutiveCofibers {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    (multiRealizationFunctor r).obj (weakStringModel q ⦋n⦌) ⟶
      ∏ᶜ (fun _ : Fin n =>
        (multiRealizationFunctor r).obj (closedStableModel (kernelClosedPredicate q))) :=
  Pi.lift (fun i => weakStringCofiberMultiMap q (consecutiveWeakStringEdge n i) r)

/-- 各積射影は元の指定連続辺の cofiber 射を厳密に回収する。 -/
lemma weakStringConsecutiveCofibers_projection {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) (i : Fin n) :
    weakStringConsecutiveCofibers q n r ≫ Pi.π _ i =
      weakStringCofiberMultiMap q (consecutiveWeakStringEdge n i) r :=
  Pi.lift_comp_π _ _

/-- 初期頂点と全ての連続 cofiber による、元の有限列全体の比較。 -/
def weakStringFiniteComparison {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    (multiRealizationFunctor r).obj (weakStringModel q ⦋n⦌) ⟶
      (multiRealizationFunctor r).obj
        (closedStableModel (ClosedStablePredicate.top (sInputModel B))) ⊗
        ∏ᶜ (fun _ : Fin n =>
          (multiRealizationFunctor r).obj (closedStableModel (kernelClosedPredicate q))) :=
  lift ((multiRealizationFunctor r).map (weakStringVertexTopExact q ⦋n⦌ 0))
    (weakStringConsecutiveCofibers q n r)

/-- 比較の第一成分は、元の初期頂点の完全な評価の実現射。 -/
lemma weakStringFiniteComparison_initial {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n r : ℕ) : weakStringFiniteComparison q n r ≫ fst _ _ =
      (multiRealizationFunctor r).map (weakStringVertexTopExact q ⦋n⦌ 0) := lift_fst _ _

/-- 比較の各 cofiber 成分は、元の同じ連続辺の共通補完の実現射。 -/
lemma weakStringFiniteComparison_cofiber {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (n r : ℕ) (i : Fin n) : weakStringFiniteComparison q n r ≫ snd _ _ ≫ Pi.π _ i =
      weakStringCofiberMultiMap q (consecutiveWeakStringEdge n i) r := by
  unfold weakStringFiniteComparison
  rw [← Category.assoc, lift_snd]
  exact weakStringConsecutiveCofibers_projection q n r i

/-- 列の任意の制限後の初期成分は、元の列の対応する頂点評価である。 -/
lemma weakStringFiniteComparison_reindex_initial {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (r : ℕ) :
    (multiRealizationFunctor r).map (weakStringExactMap q θ) ≫
      weakStringFiniteComparison q m r ≫ fst _ _ =
        (multiRealizationFunctor r).map (weakStringVertexTopExact q ⦋n⦌ (θ.toOrderHom 0)) := by
  rw [weakStringFiniteComparison_initial, ← Functor.map_comp, weakStringVertexTopExact_reindex]

/-- 制限後の各 cofiber 成分は、元の列の実合成辺への共通 cofiber 射である。 -/
lemma weakStringFiniteComparison_reindex_cofiber {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (r : ℕ) (i : Fin m) :
    (multiRealizationFunctor r).map (weakStringExactMap q θ) ≫
      weakStringFiniteComparison q m r ≫ snd _ _ ≫ Pi.π _ i =
        weakStringCofiberMultiMap q (consecutiveWeakStringEdge m i ≫ θ) r := by
  rw [weakStringFiniteComparison_cofiber, weakStringCofiberMultiMap_reindex]

end SerrePositivity.KST.Fibration
