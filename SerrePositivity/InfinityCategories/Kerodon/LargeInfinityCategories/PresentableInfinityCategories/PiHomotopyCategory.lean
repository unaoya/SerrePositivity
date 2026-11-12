module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PiQuasicategory
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
概要：小さい全直積のホモトピー圏の射を元の全成分の射で表示する。
方針：辺の代表と合成二単体を成分ごとに選び、全直積へまとめる。
規約：有限積に限定せず、元の両端点を保持する。
使われ方：小さい族の全随伴の直積構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：直積の元の二頂点間の射を全成分へ写す。
方針：各指定射影のホモトピー圏関手を使う。
規約：元の両頂点。使われ方：直積内の二胞体の検出。 -/
def piSSetHoHomMap {ι : Type u} {C : ι → SSet.{u + 1}}
    (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C) _⦋0⦌) :
    (HomotopyCategory.mk x ⟶ HomotopyCategory.mk y) →
      ∀ i, (HomotopyCategory.mk (x i) ⟶ HomotopyCategory.mk (y i)) :=
  fun α i ↦ (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i)).toFunctor.map α

/-- 概要：直積の射は全成分の射の任意の族を表示できる。
方針：各成分の一本の辺の代表を全直積へまとめる。
規約：各点の端点を保持する。使われ方：小さい全直積の Hom 対応。 -/
lemma piSSetHoHomMap_surjective {ι : Type u} {C : ι → SSet.{u + 1}}
    [∀ i, Quasicategory (C i)] (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C) _⦋0⦌) :
    Function.Surjective (piSSetHoHomMap x y) := by
  intro α
  choose e he using fun i ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (x i) (y i) (α i)
  let a : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C)) x y :=
    ⟨fun i ↦ (e i).edge, by funext i; exact (e i).src_eq,
      by funext i; exact (e i).tgt_eq⟩
  refine ⟨Truncated.HomotopyCategory.homMk a, ?_⟩
  funext i
  exact he i

/-- 概要：直積の射は全成分の射によって一意に決まる。
方針：成分ごとの辺の等式を合成二単体に戻し、同じ左ホモトピーを全直積に作る。
規約：全ての元の成分を使う。使われ方：直積の三角恒等式の検証。 -/
lemma piSSetHoHomMap_injective {ι : Type u} {C : ι → SSet.{u + 1}}
    [∀ i, Quasicategory (C i)] (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C) _⦋0⦌) :
    Function.Injective (piSSetHoHomMap x y) := by
  intro α β h
  obtain ⟨a, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y α
  obtain ⟨b, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y β
  have hi (i : ι) : Truncated.HomotopyCategory.homMk
      (a.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i))) =
      Truncated.HomotopyCategory.homMk
        (b.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i))) := congrFun h i
  have hs (i : ι) : Nonempty (Truncated.Edge.CompStruct
      (a.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i)))
      (Truncated.Edge.id (X := (truncation 2).obj (C i)) (y i))
      (b.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i)))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac
      (g := Truncated.Edge.id (X := (truncation 2).obj (C i)) (y i))
      (by simpa using hi i)
  let s (i : ι) := Classical.choice (hs i)
  let t : Truncated.Edge.CompStruct a
      (Truncated.Edge.id (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C)) y) b := {
    simplex := fun i ↦ (s i).simplex
    d₂ := by funext i; exact (s i).d₂
    d₀ := by funext i; exact (s i).d₀
    d₁ := by funext i; exact (s i).d₁ }
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopic_path_eq _ ⟨t⟩

/-- 概要：直積内の元の Hom は全成分の Hom の全直積と全単射。
方針：元の射影の全射性と単射性をまとめる。
規約：全単射の順方向は元の全射影。
使われ方：小さい全直積の全随伴の構成。 -/
def piSSetHoHomEquiv {ι : Type u} {C : ι → SSet.{u + 1}}
    [∀ i, Quasicategory (C i)] (x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C) _⦋0⦌) :
    (HomotopyCategory.mk x ⟶ HomotopyCategory.mk y) ≃
      ∀ i, (HomotopyCategory.mk (x i) ⟶ HomotopyCategory.mk (y i)) :=
  Equiv.ofBijective (piSSetHoHomMap x y)
    ⟨piSSetHoHomMap_injective x y, piSSetHoHomMap_surjective x y⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
