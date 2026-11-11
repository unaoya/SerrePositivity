module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialNerveStages
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
概要：任意の増大する共終な有限始区間から可算 nerve 上の全図式を貼り合わせる。
方針：選んだ始区間の和が全 nerve であることを示し、その余極限の普遍性を使う。
規約：選んだ段階の全自然変換を厳密に回収する。
使われ方：二段ずつ延長する全交互前置図式と増大余錐の貼り合わせ。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：共終な自然数段階の有限始区間は可算 nerve 全体を覆う。
方針：単体の有限頂点の最大値を超える選択段階を取る。
規約：全次数の部分複体としての等式。
使われ方：可算図式の共終な部分段階からの貼り合わせ。 -/
lemma iSup_sequentialNerveStage_cofinal (d : ℕ → ℕ)
    (hd : ∀ m, ∃ n, m ≤ d n) :
    (⨆ n, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage.{u} (d n)) = ⊤ := by
  apply le_antisymm le_top
  intro k s _
  obtain ⟨n, hn⟩ := hd (Finset.univ.sup (fun i ↦ (s.obj i).down))
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
  refine ⟨n, fun i ↦ ?_⟩
  exact (Finset.le_sup (f := fun j : Fin (k.unop.len + 1) ↦ (s.obj j).down)
    (Finset.mem_univ i)).trans hn

/-- 概要：増大する共終な有限始区間上の整合する全図式を貼り合わせる。
方針：部分複体の余極限と全射の整合から一つの射を構成する。
規約：quasicategory 性を仮定せず、各段階の全射を厳密に回収する。
使われ方：交互段の偶数段階のみから全可算図式を構成する。 -/
lemma exists_sequentialNerve_map_cofinalStages {X : SSet.{u}}
    (d : ℕ → ℕ) (hm : Monotone d) (hd : ∀ m, ∃ n, m ≤ d n)
    (f : ∀ n, (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage.{u} (d n) : SSet.{u}) ⟶ X)
    (hf : ∀ n m (h : n ≤ m),
      Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage_monotone (hm h)) ≫ f m = f n) :
    ∃ F : nerve (ULift.{u} ℕ) ⟶ X, ∀ n,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage (d n)).ι ≫ F = f n := by
  let D := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage_monotone.{u}.comp hm).functor
  have htop : IsLUB (Set.range D.obj) ⊤ := by
    change IsLUB (Set.range (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage.{u} (d n))) ⊤
    rw [← iSup_sequentialNerveStage_cofinal d hd]
    exact isLUB_iSup
  let c := Preorder.colimitCoconeOfIsLUB D htop
  have hc := isColimitOfPreserves Subcomplex.toSSetFunctor c.isColimit
  let e : Cocone (D ⋙ Subcomplex.toSSetFunctor) :=
    { pt := X
      ι := { app := f
             naturality := fun n m h ↦ by
               change Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage_monotone (hm (leOfHom h))) ≫
                 f m = f n ≫ 𝟙 X
               rw [Category.comp_id]
               exact hf n m (leOfHom h) } }
  refine ⟨(Subcomplex.topIso _).inv ≫ hc.desc e, ?_⟩
  intro n
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage (d n)).ι ≫ (Subcomplex.topIso _).inv =
      (Subcomplex.toSSetFunctor.mapCocone c.cocone).ι.app n := rfl
  rw [← Category.assoc, he, hc.fac]

/-- 概要：共終な有限始区間の隣接段だけの全整合から可算図式を貼り合わせる。
方針：隣接整合を自然変換にまとめ、その自然性から任意の二段の整合を得る。
規約：隣接段の全射の厳密な等式を要求する。
使われ方：可算再帰で作った交互有限段列を一つの全図式にする。 -/
lemma exists_sequentialNerve_map_cofinalStageSteps {X : SSet.{u}}
    (d : ℕ → ℕ) (hm : Monotone d) (hd : ∀ m, ∃ n, m ≤ d n)
    (f : ∀ n, (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage.{u} (d n) : SSet.{u}) ⟶ X)
    (hf : ∀ n, Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage_monotone (hm (Nat.le_succ n))) ≫
      f (n + 1) = f n) :
    ∃ F : nerve (ULift.{u} ℕ) ⟶ X, ∀ n,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage (d n)).ι ≫ F = f n := by
  let D := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage_monotone.{u}.comp hm).functor ⋙ Subcomplex.toSSetFunctor
  let η : D ⟶ (CategoryTheory.Functor.const ℕ).obj X :=
    NatTrans.ofSequence (fun n ↦ f n) (fun n ↦ by
      change Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage_monotone (hm (Nat.le_succ n))) ≫
        f (n + 1) = f n ≫ 𝟙 X
      simpa only [Category.comp_id] using hf n)
  apply exists_sequentialNerve_map_cofinalStages d hm hd f
  intro n m h
  have he := η.naturality (homOfLE h)
  change Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveStage_monotone (hm h)) ≫ f m = f n ≫ 𝟙 X at he
  simpa only [Category.comp_id] using he

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
