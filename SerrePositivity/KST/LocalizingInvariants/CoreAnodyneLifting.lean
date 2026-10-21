module

public import SerrePositivity.InfinityCategories.F2.CoreIsofibration

/-!
概要：core に入る指定図式は、anodyne 射に沿って底を固定したまま延長できる。
方針：同値を持ち上げる関手の core は Kan fibration なので、元の正方形を持ち上げる。
規約：追加のモデル圏仮定を置かない。使われ方：可逆区間の相対的な延長と商の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma exists_coreAnodyne_lift {A B X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (p : X ⟶ Y) (hp : F1B.KanEquivalenceLifting p) (j : A ⟶ B)
    (hj : anodyneExtensions j) (f : A ⟶ X) (g : B ⟶ Y)
    (hf : ∀ s : A _⦋1⦌, IsInvertibleEdge (edgeOfSimplex (f.app (Opposite.op ⦋1⦌) s)))
    (hg : ∀ s : B _⦋1⦌, IsInvertibleEdge (edgeOfSimplex (g.app (Opposite.op ⦋1⦌) s)))
    (h : f ≫ p = j ≫ g) : ∃ l : B ⟶ X, j ≫ l = f ∧ l ≫ p = g := by
  have : Fibration (quasicategoryCoreMap p) :=
    F2.coreMap_fibration_of_kanEquivalenceLifting p hp
  have : HasLiftingProperty j (quasicategoryCoreMap p) := by
    rw [anodyneExtensions_eq_llp_rlp] at hj
    exact hj _ ((fibration_iff _).mp inferInstance)
  let sq : CommSq (quasicategoryCoreLift f hf) j (quasicategoryCoreMap p)
      (quasicategoryCoreLift g hg) := ⟨by
    apply (cancel_mono (quasicategoryCore Y).ι).mp
    simp only [Category.assoc, quasicategoryCoreMap_ι, quasicategoryCoreLift_ι]
    rw [← Category.assoc, quasicategoryCoreLift_ι, h]⟩
  refine ⟨sq.lift ≫ (quasicategoryCore X).ι, ?_, ?_⟩
  · rw [← Category.assoc, sq.fac_left, quasicategoryCoreLift_ι]
  · rw [Category.assoc, ← quasicategoryCoreMap_ι, ← Category.assoc, sq.fac_right,
      quasicategoryCoreLift_ι]

/-- Kan な始域からの射の全ての辺は可逆。 -/
lemma kanSource_map_invertible {A X : SSet.{u}} [KanComplex A] (f : A ⟶ X)
    (s : A _⦋1⦌) : IsInvertibleEdge (edgeOfSimplex (f.app (Opposite.op ⦋1⦌) s)) := by
  have hs : IsInvertibleEdge (edgeOfSimplex s) :=
    @IsGroupoid.all_isIso (hoFunctor.obj A) _ (kanComplex_ho_isGroupoid A) _ _ _
  exact (isInvertibleEdge_congr (e := (edgeOfSimplex s).map ((truncation 2).map f))
    (f := edgeOfSimplex (f.app (Opposite.op ⦋1⦌) s)) rfl).mp (hs.map f)

end SerrePositivity.KST.LocalizingInvariants
