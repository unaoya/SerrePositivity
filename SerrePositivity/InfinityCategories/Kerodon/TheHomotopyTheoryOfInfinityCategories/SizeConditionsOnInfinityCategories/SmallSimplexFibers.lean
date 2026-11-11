module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningSmallness
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationTensor
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
概要：射影の各次数の fiber の小ささと任意の底変換での保存。
方針：指定した底の単体上の逆像を小さい型として扱い pullback の単射で移す。
規約：底と全空間の各次数自体は大きくてもよい。
使われ方：任意の底上の表現空間の可縮性と写像空間比較。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 概要：射影の各次数の各単体上の fiber が小さいという条件。
方針：次数ごとの写像の指定単体の逆像を使う。
規約：小ささの宇宙 u と単体集合の宇宙 u+1 を区別する。
使われ方：底の小ささを仮定しない表現の延長の入力。 -/
def HasSmallSimplexFibers {E B : SSet.{u + 1}} (p : E ⟶ B) : Prop :=
  ∀ (n : SimplexCategoryᵒᵖ) (b : B.obj n), Small.{u} {x : E.obj n // p.app n x = b}

/-- 概要：小さい全空間の射影は小さい次数 fiber を持つ。
方針：部分型の小ささ。
規約：底の小ささは不要。
使われ方：既存の小さい全空間の定理との接続。 -/
lemma hasSmallSimplexFibers_of_small_total {E B : SSet.{u + 1}}
    [∀ n, Small.{u} (E.obj n)] (p : E ⟶ B) : HasSmallSimplexFibers p := by
  intro n b
  infer_instance

/-- 概要：小さい底と小さい次数 fiber を持つ射影の全空間は小さい。
方針：底の単体で添字付けた fiber の直和へ単射で符号化する。
規約：各次数を独立に扱う。
使われ方：標準単体と境界への底変換の全空間の小ささ。 -/
lemma HasSmallSimplexFibers.total_obj_small {E B : SSet.{u + 1}} {p : E ⟶ B}
    (hp : HasSmallSimplexFibers p) (n : SimplexCategoryᵒᵖ) [Small.{u} (B.obj n)] :
    Small.{u} (E.obj n) := by
  have (b : B.obj n) : Small.{u} {x : E.obj n // p.app n x = b} := hp n b
  let T := Σ b : B.obj n, {x : E.obj n // p.app n x = b}
  let code : E.obj n → T := fun x ↦ ⟨p.app n x, x, rfl⟩
  apply small_of_injective (f := code)
  intro x y h
  exact congrArg (fun t : T ↦ t.2.val) h

/-- 概要：小さい次数 fiber の条件は cartesian 正方形で保存される。
方針：新しい fiber を元の fiber へ単射で入れ pullback の外延性で検査する。
規約：両方の射影に充填性は不要。
使われ方：底変換とパラメーターとの積の統一した保存則。 -/
lemma HasSmallSimplexFibers.of_isPullback {E F B D : SSet.{u + 1}}
    {p : E ⟶ B} (hp : HasSmallSimplexFibers p)
    {e : F ⟶ E} {q : F ⟶ D} {g : D ⟶ B} (h : IsPullback e q p g) :
    HasSmallSimplexFibers q := by
  intro n d
  have : Small.{u} {x : E.obj n // p.app n x = g.app n d} := hp n (g.app n d)
  let code : {x : F.obj n // q.app n x = d} →
      {x : E.obj n // p.app n x = g.app n d} := fun x ↦ ⟨e.app n x.val, by
        have hc := ConcreteCategory.congr_hom (C := Type (u + 1)) (NatTrans.congr_app h.w n) x.val
        change p.app n (e.app n x.val) = g.app n (q.app n x.val) at hc
        exact hc.trans (congrArg (fun a ↦ g.app n a) x.property)⟩
  apply small_of_injective (f := code)
  intro x y he
  apply Subtype.ext
  apply Types.ext_of_isPullback (h.app n)
  · exact congrArg Subtype.val he
  · exact x.property.trans y.property.symm

/-- 概要：任意の底変換で次数 fiber の小ささは保存される。
方針：標準 pullback の cartesian 正方形を使う。
規約：底変換先の大きさに制限はない。
使われ方：標準単体と部分複体への制限。 -/
lemma HasSmallSimplexFibers.pullback_snd {E B D : SSet.{u + 1}} {p : E ⟶ B}
    (hp : HasSmallSimplexFibers p) (g : D ⟶ B) : HasSmallSimplexFibers (pullback.snd p g) :=
  hp.of_isPullback (IsPullback.of_hasPullback p g)

/-- 概要：逆順の標準 pullback も小さい次数 fiber を持つ。
方針：標準の正方形の対称性を使う。
規約：底変換先が第一因子。
使われ方：セル帰納法の底変換の表示。 -/
lemma HasSmallSimplexFibers.pullback_fst {E B D : SSet.{u + 1}} {p : E ⟶ B}
    (hp : HasSmallSimplexFibers p) (g : D ⟶ B) : HasSmallSimplexFibers (pullback.fst g p) :=
  hp.of_isPullback (IsPullback.of_hasPullback g p).flip

/-- 概要：任意のパラメーターとの積は小さい次数 fiber の条件を保つ。
方針：第一射影の cartesian 正方形を使う。
規約：パラメーター自体の小ささは不要。
使われ方：大きい写像空間をパラメーターとする普遍的な族。 -/
lemma HasSmallSimplexFibers.tensor {E B : SSet.{u + 1}} {p : E ⟶ B}
    (hp : HasSmallSimplexFibers p) (K : SSet.{u + 1}) : HasSmallSimplexFibers (p ▷ K) :=
  hp.of_isPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isPullback_tensor_fst p K)

/-- 概要：普遍的な pointed-space 射影は小さい次数 fiber を持つ。
方針：普遍射影の各単体上の小ささの定理を束ねる。
規約：底の空間全体の大きさは変えない。
使われ方：任意の底上の coherent な図式への適用。 -/
lemma pointedSpaceProjection_hasSmallSimplexFibers :
    HasSmallSimplexFibers _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection.{u} := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceProjection_simplexFiber_small

/-- 概要：任意の底上の coherent な図式の unstraightening は小さい次数 fiber を持つ。
方針：普遍的な pointed-space 射影の底変換。
規約：底の小ささは不要。
使われ方：任意の底上の写像空間比較の入力。 -/
lemma leftUnstraighteningProjection_hasSmallSimplexFibers {B : SSet.{u + 1}}
    (F : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) : HasSmallSimplexFibers (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) :=
  pointedSpaceProjection_hasSmallSimplexFibers.pullback_snd F

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
