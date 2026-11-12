module

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
概要：単体集合の小さい余積を次数ごとの直和で具体的に構成する。
方針：成分添字を全ての面・退化で保持し、包含と降下射を成分ごとに定義する。
規約：空の添字も含め、単体の宇宙は添字と同じ u。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB） の Kan 複体の実際の余積の台。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {J : Type u}

/-- 概要：単体集合の族の次数ごとの直和。
方針：単体に成分添字を添え、構造射はその成分で作用させる。
規約：空族では全次数が空。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、𝒮 の実際の余積の対象。 -/
def simplicialCoproduct (F : J → SSet.{u}) : SSet.{u} where
  obj n := Σ j, (F j).obj n
  map a := ↾fun s ↦ ⟨s.1, (F s.1).map a s.2⟩

/-- 概要：各成分から次数ごとの直和への標準包含。
方針：全ての単体に固定した添字を付ける。
規約：単体的写像として構成する。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、余積錐の各脚。 -/
def simplicialCoproductι (F : J → SSet.{u}) (j : J) : F j ⟶ simplicialCoproduct F where
  app _ := ↾fun s ↦ ⟨j, s⟩

/-- 概要：直和の各成分からの射は直和からの降下射を定める。
方針：成分添字で場合分けして与えた射を適用する。
規約：値域 X は任意の単体集合。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、台の余積の普遍性。 -/
def simplicialCoproductDesc (F : J → SSet.{u}) {X : SSet.{u}}
    (f : ∀ j, F j ⟶ X) : simplicialCoproduct F ⟶ X where
  app n := ↾fun s ↦ (f s.1).app n s.2
  naturality _ _ a := by
    ext s
    exact ConcreteCategory.congr_hom ((f s.1).naturality a) s.2

/-- 概要：直和の降下射を各成分へ制限すると元の射になる。
方針：各次数の単体で定義を計算する。
規約：厳密な射の等式。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、余積の普遍射の成分。 -/
lemma simplicialCoproductι_desc (F : J → SSet.{u}) {X : SSet.{u}}
    (f : ∀ j, F j ⟶ X) (j : J) :
    simplicialCoproductι F j ≫ simplicialCoproductDesc F f = f j := rfl

/-- 概要：直和からの二つの射は各成分への制限で一致を検出できる。
方針：単体の成分添字を取り出して与えた等式を評価する。
規約：添字の非空性を仮定しない。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、直和の普遍射の一意性。 -/
lemma simplicialCoproduct_hom_ext (F : J → SSet.{u}) {X : SSet.{u}}
    {f g : simplicialCoproduct F ⟶ X}
    (h : ∀ j, simplicialCoproductι F j ≫ f = simplicialCoproductι F j ≫ g) : f = g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨j, s⟩
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (h j) n) s

/-- 概要：一つの成分への二つの射は直和に含めた後で一致を検出できる。
方針：各次数で直和の同じ成分への包含の単射性を使う。
規約：始域 X に条件を要求しない。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、ホーンの成分内での整合性。 -/
lemma simplicialCoproductι_cancel (F : J → SSet.{u}) (j : J) {X : SSet.{u}}
    {f g : X ⟶ F j} (h : f ≫ simplicialCoproductι F j = g ≫ simplicialCoproductι F j) :
    f = g := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  exact eq_of_heq (Sigma.mk.inj (ConcreteCategory.congr_hom
    (NatTrans.congr_app h n) s)).2

/-- 概要：直和の標準包含からなる余錐は単体集合の余積余錐。
方針：成分ごとの降下射と射の外延性で普遍性を示す。
規約：全ての小さい族と空族を含む。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、Kan 複体の余積の台の普遍性。 -/
def simplicialCoproduct_isColimit (F : J → SSet.{u}) :
    IsColimit (Cofan.mk (simplicialCoproduct F) (simplicialCoproductι F)) where
  desc s := simplicialCoproductDesc F (fun j ↦ s.ι.app ⟨j⟩)
  fac _ _ := rfl
  uniq s m hm := simplicialCoproduct_hom_ext F (fun j ↦ by
    exact (hm ⟨j⟩).trans (simplicialCoproductι_desc F (fun j ↦ s.ι.app ⟨j⟩) j).symm)

/-- 概要：直和の単体の成分添字は面を取っても変わらない。
方針：Yoneda の面の計算と直和の構造射の定義を使う。
規約：任意の正次元の標準単体からの射を扱う。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、ホーンの全ての面の成分の照合。 -/
lemma simplicialCoproduct_simplexLabel_face (F : J → SSet.{u}) {n : ℕ}
    (f : (Δ[n + 1] : SSet.{u}) ⟶ simplicialCoproduct F) (j : Fin (n + 2)) :
    (SSet.yonedaEquiv (stdSimplex.δ j ≫ f)).1 = (SSet.yonedaEquiv f).1 := by
  rw [stdSimplex.yonedaEquiv_δ_comp]
  rfl

/-- 概要：直和への標準単体は指定した成分添字が一致すればその成分を経由する。
方針：Yoneda で単体を取り出し、第二成分から標準単体の射を復元する。
規約：成分添字の等号を仮定し、非空性を別に仮定しない。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、ホーンを一つの Kan 成分に戻す構成。 -/
lemma simplicialCoproduct_simplex_factorization (F : J → SSet.{u}) {n : ℕ}
    (f : (Δ[n] : SSet.{u}) ⟶ simplicialCoproduct F) (j : J)
    (h : (SSet.yonedaEquiv f).1 = j) :
    ∃ g : (Δ[n] : SSet.{u}) ⟶ F j, g ≫ simplicialCoproductι F j = f := by
  subst j
  refine ⟨SSet.yonedaEquiv.symm (SSet.yonedaEquiv f).2, ?_⟩
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
