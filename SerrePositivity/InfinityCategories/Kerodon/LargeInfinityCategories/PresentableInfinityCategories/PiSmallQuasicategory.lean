module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone

/-!
概要：同じ宇宙の族の全直積を各次数の全関数として構成する。
方針：元の各射影と成分ごとの内ホーン充填を使う。
規約：添字は u、因子と直積の単体は u。
使われ方：小さい底の直和上の前層圏の積表示。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：小さい族の元の各次数の直積。
方針：再添字は各成分へ作用する。
規約：全高次単体を保持する。
使われ方：presentable 圏の小さい積模型。 -/
def piSSetSmall {ι : Type u} (C : ι → SSet.{u}) : SSet.{u} where
  obj n := ∀ i, (C i).obj n
  map α := ↾fun x i ↦ (C i).map α (x i)
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    exact CategoryTheory.Functor.map_id_apply (C i) n (x i)
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    exact CategoryTheory.Functor.map_comp_apply (C i) α β (x i)

/-- 概要：小さい全直積からの元の指定射影。
方針：全関数を指定添字で評価する。
規約：元の各次数の成分。
使われ方：ホーン充填と関手の成分計算。 -/
def piSSetSmallProjection {ι : Type u} (C : ι → SSet.{u}) (i : ι) : piSSetSmall C ⟶ C i where
  app _ := ↾fun x ↦ x i
  naturality _ _ _ := rfl

/-- 概要：指定した全成分への射を元の全直積へまとめる。
方針：各次数で全ての成分を並べる。
規約：同じ始域 K を使う。
使われ方：各成分のホーン充填の統合。 -/
def piSSetSmallLift {ι : Type u} {C : ι → SSet.{u}} {K : SSet.{u}}
    (f : ∀ i, K ⟶ C i) : K ⟶ piSSetSmall C where
  app n := ↾fun x i ↦ (f i).app n x
  naturality _ _ α := by
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    exact ConcreteCategory.congr_hom (C := Type u) ((f i).naturality α) x

/-- 概要：元の直積へまとめて射影すると指定した成分。
方針：各次数で評価する。
規約：全射の等式。
使われ方：直積の普遍性とホーン充填。 -/
lemma piSSetSmallLift_projection {ι : Type u} {C : ι → SSet.{u}} {K : SSet.{u}}
    (f : ∀ i, K ⟶ C i) (i : ι) :
    piSSetSmallLift f ≫ piSSetSmallProjection C i = f i := rfl

/-- 概要：元の全直積の射は全ての成分で決まる。
方針：各次数の関数外延性を使う。
規約：全形状 K を扱う。
使われ方：指定された直積模型の厳密な比較。 -/
lemma piSSetSmall_hom_ext {ι : Type u} {C : ι → SSet.{u}} {K : SSet.{u}}
    {f g : K ⟶ piSSetSmall C}
    (h : ∀ i, f ≫ piSSetSmallProjection C i = g ≫ piSSetSmallProjection C i) :
    f = g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  funext i
  exact congrArg (fun q ↦ q.app n x) (h i)

/-- 概要：小さい quasicategory の族の元の全直積も quasicategory。
方針：各指定射影で埋めたホーンを全直積へまとめる。
規約：添字の有限性は要求しない。
使われ方：前層の積模型と Pr^L の小さい積。 -/
instance piSSetSmall_quasicategory {ι : Type u} (C : ι → SSet.{u})
    [∀ i, Quasicategory (C i)] : Quasicategory (piSSetSmall C) := by
  constructor
  intro n k a h0 hn
  choose s hs using fun i ↦ Quasicategory.hornFilling h0 hn (a ≫ piSSetSmallProjection C i)
  refine ⟨piSSetSmallLift s, ?_⟩
  apply piSSetSmall_hom_ext
  intro i
  simpa only [Category.assoc, piSSetSmallLift_projection] using hs i

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
