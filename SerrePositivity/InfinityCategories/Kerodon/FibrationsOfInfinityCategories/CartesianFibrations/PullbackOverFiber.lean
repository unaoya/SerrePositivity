module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：共通の底上の引き戻しの fiber を fiber の引き戻しと同定する。
方針：包含へ合成して三つの fiber の可換性と引き戻しの普遍性を照合する。
規約：射と単体集合に充填性を仮定しない。
使われ方：関手の全空間の相対比較の標的の fiber の計算。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：底を保つ二つの射の引き戻しの両射影からの底射影は一致する。
方針：引き戻し条件へ共通の底への射を後合成する。
規約：第一射影から底射影を定義する。
使われ方：第二射影の fiber への制限。 -/
lemma pullbackOver_snd_projection {X Y Z C : SSet.{u}}
    (p : X ⟶ C) (q : Y ⟶ C) (r : Z ⟶ C) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : f ≫ r = p) (hg : g ≫ r = q) :
    pullback.snd f g ≫ q = pullback.fst f g ≫ p := by
  rw [← hf, ← hg, ← Category.assoc, ← Category.assoc, pullback.condition]

/-- 概要：共通の底上の引き戻しの fiber の二射影も引き戻しを与える。
方針：二つの fiber の射を全空間の引き戻しへ合わせ、底が定値なことから fiber へ戻す。
規約：選んだ底頂点は任意。
使われ方：相対比較の標的の fiber の標準表示。 -/
lemma pullbackOver_fiber_isPullback {X Y Z C : SSet.{u}}
    (p : X ⟶ C) (q : Y ⟶ C) (r : Z ⟶ C) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : f ≫ r = p) (hg : g ≫ r = q) (c : C _⦋0⦌) :
    IsPullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (pullback.fst f g ≫ p) p (pullback.fst f g) rfl c)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap (pullback.fst f g ≫ p) q (pullback.snd f g)
        (pullbackOver_snd_projection p q r f g hf hg) c)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p r f hf c) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap q r g hg c) := by
  let R := pullback.fst f g ≫ p
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap R p (pullback.fst f g) rfl c
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap R q (pullback.snd f g)
    (pullbackOver_snd_projection p q r f g hf hg) c
  have ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι R c ≫ pullback.fst f g :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι _ _ _ _ _
  have hb : b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q c = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι R c ≫ pullback.snd f g :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι _ _ _ _ _
  change IsPullback a b (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p r f hf c) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap q r g hg c)
  apply IsPullback.mk'
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext r c
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
    erw [reassoc_of% ha, reassoc_of% hb]
    exact congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι R c ≫ z) (pullback.condition (f := f) (g := g))
  · intro T u v h₁ h₂
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext R c
    apply pullback.hom_ext
    · have h := congrArg (fun z ↦ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c) h₁
      simpa only [Category.assoc, ha] using h
    · have h := congrArg (fun z ↦ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q c) h₂
      simpa only [Category.assoc, hb] using h
  · intro T u v huv
    have hw : (u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c) ≫ f = (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q c) ≫ g := by
      have h := congrArg (fun z ↦ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι r c) huv
      simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι] using h
    let l := pullback.lift (u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c) (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q c) hw
    have hl : l ≫ R = SSet.const c := by
      dsimp only [R, l]
      rw [← Category.assoc, pullback.lift_fst, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift R c l hl, ?_, ?_⟩
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p c
      rw [Category.assoc, ha, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
      exact pullback.lift_fst _ _ _
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q c
      rw [Category.assoc, hb, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
      exact pullback.lift_snd _ _ _

/-- 概要：共通の底上の引き戻しの fiber は fiber の引き戻しと同型。
方針：fiber の引き戻し表示から標準の引き戻しへの同型を取る。
規約：同型は元の二つの射影を保持する。
使われ方：相対関手の族の fiber の標的を通常の関手圏の引き戻しへ移す。 -/
def pullbackOverFiberIso {X Y Z C : SSet.{u}}
    (p : X ⟶ C) (q : Y ⟶ C) (r : Z ⟶ C) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : f ≫ r = p) (hg : g ≫ r = q) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (pullback.fst f g ≫ p) c ≅
      pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p r f hf c) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap q r g hg c) :=
  (pullbackOver_fiber_isPullback p q r f g hf hg c).isoPullback

/-- 概要：交換同型の逆射は第一射影を保つ。
方針：引き戻し表示の同型の第一射影の式へ fiber の包含を合成する。
規約：底射影は全空間の第一射影で定義する。
使われ方：相対比較の図式成分の同定。 -/
@[reassoc]
lemma pullbackOverFiberIso_inv_fst {X Y Z C : SSet.{u}}
    (p : X ⟶ C) (q : Y ⟶ C) (r : Z ⟶ C) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : f ≫ r = p) (hg : g ≫ r = q) (c : C _⦋0⦌) :
    (pullbackOverFiberIso p q r f g hf hg c).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (pullback.fst f g ≫ p) c ≫ pullback.fst f g =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p r f hf c) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap q r g hg c) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι (pullback.fst f g ≫ p) p (pullback.fst f g) rfl c,
    ← Category.assoc]
  exact congrArg (fun z ↦ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c)
    (pullbackOver_fiber_isPullback p q r f g hf hg c).isoPullback_inv_fst

/-- 概要：交換同型の逆射は第二射影を保つ。
方針：引き戻し表示の同型の第二射影の式へ fiber の包含を合成する。
規約：第二射影も同じ底の fiber へ制限する。
使われ方：相対比較の標的の余錐成分の同定。 -/
@[reassoc]
lemma pullbackOverFiberIso_inv_snd {X Y Z C : SSet.{u}}
    (p : X ⟶ C) (q : Y ⟶ C) (r : Z ⟶ C) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : f ≫ r = p) (hg : g ≫ r = q) (c : C _⦋0⦌) :
    (pullbackOverFiberIso p q r f g hf hg c).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (pullback.fst f g ≫ p) c ≫ pullback.snd f g =
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p r f hf c) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap q r g hg c) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q c := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι (pullback.fst f g ≫ p) q (pullback.snd f g)
    (pullbackOver_snd_projection p q r f g hf hg) c, ← Category.assoc]
  exact congrArg (fun z ↦ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q c)
    (pullbackOver_fiber_isPullback p q r f g hf hg c).isoPullback_inv_snd

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
