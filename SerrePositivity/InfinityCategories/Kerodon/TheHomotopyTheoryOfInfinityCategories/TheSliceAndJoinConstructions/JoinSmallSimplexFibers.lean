module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallSimplexFiberOperations
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-!
概要：小さい次数 fiber の条件は join によって保たれる。
方針：切断位置を固定した fiber を左右の補った単体の fiber の積で符号化する。
規約：因子の単体集合自体や添字の全体の小ささは不要。
使われ方：任意の底上の相対射の collage の次数 fiber の小ささ。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：直積の写像の fiber は両側の fiber が小さければ小さい。
方針：両側の fiber の積へ単射で入れる。
規約：元の型全体の小ささは不要。
使われ方：join の切断位置を固定した fiber。 -/
lemma small_prod_map_fiber {A B : Type v} {C D : Type w}
    (f : A → B) (g : C → D) (b : B) (d : D)
    [Small.{u} {a : A // f a = b}] [Small.{u} {c : C // g c = d}] :
    Small.{u} {z : A × C // (f z.1, g z.2) = (b, d)} := by
  let code : {z : A × C // (f z.1, g z.2) = (b, d)} →
      {a : A // f a = b} × {c : C // g c = d} := fun z ↦
    (⟨z.val.1, congrArg Prod.fst z.property⟩, ⟨z.val.2, congrArg Prod.snd z.property⟩)
  apply small_of_injective (f := code)
  intro x y h
  exact Subtype.ext (Prod.ext (congrArg (fun z ↦ z.1.val) h) (congrArg (fun z ↦ z.2.val) h))

/-- 概要：同じ添字を保つ直和の写像の fiber は指定した添字の fiber の小ささを保つ。
方針：指定した添字から fiber 全体への全射を作る。
規約：添字全体の小ささは不要。
使われ方：join の切断位置の有限直和の fiber。 -/
lemma small_sigma_map_fiber {I : Type v} {A B : I → Type w}
    (f : ∀ i, A i → B i) (i : I) (b : B i) [Small.{u} {a : A i // f i a = b}] :
    Small.{u} {x : Σ j, A j // (⟨x.1, f x.1 x.2⟩ : Σ j, B j) = ⟨i, b⟩} := by
  let code : {a : A i // f i a = b} →
      {x : Σ j, A j // (⟨x.1, f x.1 x.2⟩ : Σ j, B j) = ⟨i, b⟩} :=
    fun a ↦ ⟨⟨i, a.val⟩, congrArg (fun c : B i ↦ Sigma.mk i c) a.property⟩
  apply small_of_surjective (f := code)
  rintro ⟨⟨j, a⟩, h⟩
  have hji : j = i := congrArg Sigma.fst h
  subst j
  have ha : f i a = b := eq_of_heq (Sigma.mk.inj h).2
  exact ⟨⟨a, ha⟩, Subtype.ext rfl⟩

/-- 概要：空単体を補っても指定単体の fiber は小さい。
方針：空単体は一点、非空単体は元の次数 fiber の条件を使う。
規約：r は頂点数。
使われ方：join の左右の係数の fiber。 -/
lemma HasSmallSimplexFibers.augHom_fiber_small {E B : SSet.{u + 1}} {p : E ⟶ B}
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers p) (r : ℕ) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj B r) :
    Small.{u} {x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj E r // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom p r x = b} := by
  cases r with
  | zero => exact inferInstanceAs (Small.{u} {x : PUnit // x = b})
  | succ r => exact hp (Opposite.op ⦋r⦌) b

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.HasSmallSimplexFibers (augHom_fiber_small)


/-- 概要：両因子の小さい次数 fiber の条件は joinMap へ移る。
方針：切断を固定して左右の fiber の積と直和の保存則を使う。
規約：各因子の全空間や底は大きくてもよい。
使われ方：relative join の pullback の射影の小ささ。 -/
lemma HasSmallSimplexFibers.joinMap {E E' F F' : SSet.{u + 1}}
    {p : E ⟶ E'} {q : F ⟶ F'} (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers p) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap p q) := by
  rintro ⟨⟨n⟩⟩ ⟨i, x, y⟩
  have := hp.augHom_fiber_small i.val x
  have := hq.augHom_fiber_small (n + 1 - i.val) y
  have := small_prod_map_fiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom p i.val)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom q (n + 1 - i.val)) x y
  exact small_sigma_map_fiber
    (fun (j : Fin (n + 2)) (z : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj E j.val × _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj F (n + 1 - j.val)) ↦
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom p j.val z.1, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom q (n + 1 - j.val) z.2)) i (x, y)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallSimplexFibers export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.HasSmallSimplexFibers (joinMap)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
