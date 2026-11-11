module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.FilledFunctor

/-!
# 充填候補のホーンへの制限

概要：復元した豊穣関手を既知の各面へ制限すると元のホーンの単体に戻る。
方針：零座標面上で全ての Hom の一致を示し、面の Hom の同型で引き戻す。
規約：全区間の端点を面の像で書く際の型の移送を避け、先に任意の端点で比較する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） の内部ホーン充填の境界条件。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.SimplicialThickening
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]
variable {n : ℕ} {i : Fin (n + 3)}

/-- 概要：充填用の Hom と既知面の候補は任意の端点の零座標面上で一致する。
方針：逆向き区間は空性、真部分区間は面の Hom の同型、全区間は延長の制限則を使う。
規約：二つの端点は比較する既知面の除外点を避ける。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） の既知面の Hom の回収。 -/
lemma hornFillHom_on_zero
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (g)
    (hg : ∀ j, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollowFace (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHollowPoint.{v} i h0 hn) j).ι ≫ g =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHollowFaceHom σ h0 hn j)
    (j : Fin (n + 3)) (hj : j ≠ i) (a b : Fin (n + 3)) (haj : a ≠ j) (hbj : b ≠ j) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{v} a) (b := ULift.up b) (ULift.up j)).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFillHom σ h0 hn g a b =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathAvoids (a := ULift.up.{v} a) (b := ULift.up b) (ULift.up j)).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ j hj a b haj hbj := by
  by_cases hab : a ≤ b
  swap
  · apply CategoryTheory.NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro F
    exact (hab (F.1.obj 0).le).elim
  by_cases hp : a ≠ 0 ∨ b ≠ Fin.last (n + 2)
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFillHom_proper σ h0 hn g a b hab hp]
    obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq haj
    obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq hbj
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceIso.{v} j a b).hom).mp
    simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceIso_hom_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornProperIntervalHom_on_face σ h0 hn j hj a b
      ((Fin.strictMono_succAbove j).le_iff_le.mp hab) hp).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace_on_face σ j hj a b).symm
  have ha : a = 0 := not_not.mp (fun h ↦ hp (Or.inl h))
  have hb : b = Fin.last (n + 2) := not_not.mp (fun h ↦ hp (Or.inr h))
  subst a b
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFillHom_full]
  have hj0 : 0 < j := lt_of_le_of_ne (Fin.zero_le j) haj
  have hjn : j < Fin.last (n + 2) := lt_of_le_of_ne (Fin.le_last j) (Ne.symm hbj)
  exact hg (.inr ⟨⟨ULift.up j, hj0, hjn⟩, fun h ↦ hj (congrArg (fun x ↦ x.1.down) h)⟩)

/-- 概要：充填用の Hom を既知面へ制限するとその面からの Hom 回収に等しい。
方針：面の Hom を零座標面へ同型で送り、零座標面の比較と面候補の制限則を使う。
規約：順序外や同じ端点も含む全ての頂点対を扱う。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） の面の豊穣関手の比較。 -/
lemma hornFillHom_on_face
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (g)
    (hg : ∀ j, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollowFace (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHollowPoint.{v} i h0 hn) j).ι ≫ g =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHollowFaceHom σ h0 hn j)
    (j : Fin (n + 3)) (hj : j ≠ i) (a b : Fin (n + 2)) :
    (SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap).map
      ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFillHom σ h0 hn g (j.succAbove a) (j.succAbove b) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell σ (SSet.horn.face i j hj) a b := by
  have hz := hornFillHom_on_zero σ h0 hn g hg j hj (j.succAbove a) (j.succAbove b)
    (Fin.succAbove_ne j a) (Fin.succAbove_ne j b)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap j a b ≫ _ = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceIso_hom_ι, Category.assoc, hz, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceIso_hom_ι]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace_on_face σ j hj a b

set_option backward.isDefEq.respectTransparency false in
/-- 概要：復元した豊穣関手の各既知面は元のホーンの単体に等しい。
方針：対象比較で豊穣関手を外延し、Hom の制限の等式の後に型の移送を戻す。
規約：等式は Mathlib の SimplicialNerve の面作用について述べる。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.10（Tag 00LT） のホーン充填単体の最終境界条件。 -/
lemma hornFilledFunctor_face
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (g)
    (hg : ∀ j, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHollowFace (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHollowPoint.{v} i h0 hn) j).ι ≫ g =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHollowFaceHom σ h0 hn j) (j : Fin (n + 3)) (hj : j ≠ i) :
    (SimplicialNerve C).δ j (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFilledFunctor σ h0 hn g hg) =
      σ.app _ (SSet.horn.face i j hj) := by
  apply EnrichedFunctor.ext SSet (fun X ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.horn_face_obj σ j hj X.as.down).symm)
  intro X Y
  change ((SimplicialThickening.functor (SimplexCategory.δ j).toOrderHom.uliftMap).map
    ⟨⟨X.as.down⟩⟩ ⟨⟨Y.as.down⟩⟩ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornFillHom σ h0 hn g (j.succAbove X.as.down) (j.succAbove Y.as.down)) ≫ _ = _
  rw [hornFillHom_on_face σ h0 hn g hg j hj]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell_transport_back σ (SSet.horn.face i j hj) X.as.down Y.as.down

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
