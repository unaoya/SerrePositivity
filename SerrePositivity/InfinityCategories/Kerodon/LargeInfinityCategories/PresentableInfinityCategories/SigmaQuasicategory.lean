module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ConstantQuasicategory

/-!
概要：小さい quasicategory の族の直和を元の単体の直和として構成する。
方針：定値ラベルへの射影を使い、各内ホーンを一つの元の成分内で充填する。
規約：各次数の単体を小さい依存直和として保持する。モデル構造は使わない。
使われ方：前層の積模型の小さい底。

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

/-- 概要：小さい単体集合の族の次数ごとの直和。
方針：再添字の作用はラベルを固定する。
規約：ラベルと各単体の宇宙は共に u。
使われ方：前層の積を表す小さい底。 -/
def sigmaSSet {ι : Type u} (C : ι → SSet.{u}) : SSet.{u} where
  obj n := Σ i, (C i).obj n
  map α := ↾fun x ↦ ⟨x.1, (C x.1).map α x.2⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    rintro ⟨i, x⟩
    simp only [CategoryTheory.Functor.map_id_apply]
    rfl
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    rintro ⟨i, x⟩
    simp only [CategoryTheory.Functor.map_comp_apply]
    rfl

/-- 概要：元の直和のラベルを定値単体集合へ送る。
方針：各単体の第一成分を取る。
規約：全次数で同じラベル。
使われ方：ホーンを一つの成分へ戻す。 -/
def sigmaSSetProjection {ι : Type u} (C : ι → SSet.{u}) :
    sigmaSSet C ⟶ (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj ι where
  app _ := ↾Sigma.fst
  naturality _ _ _ := rfl

/-- 概要：指定した元の成分を直和へ含める。
方針：指定ラベルと元の単体を対にする。
規約：単体の再選択は行わない。
使われ方：成分内のホーン充填を全体へ戻す。 -/
def sigmaSSetInclusion {ι : Type u} (C : ι → SSet.{u}) (i : ι) : C i ⟶ sigmaSSet C where
  app _ := ↾fun x ↦ ⟨i, x⟩
  naturality _ _ _ := rfl

lemma sigmaValue_transport_congr {ι : Type u} {A : ι → Type u}
    {x y : Σ i, A i} {i : ι} (h : x = y) (hx : x.1 = i) (hy : y.1 = i) :
    hx ▸ x.2 = hy ▸ y.2 := by
  cases h
  rfl

lemma sigmaValue_transport_map {ι : Type u} (C : ι → SSet.{u})
    {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) (x : Σ j, (C j).obj n)
    {i : ι} (h : x.1 = i) :
    h ▸ ((C x.1).map α x.2) = (C i).map α (h ▸ x.2) := by
  rcases x with ⟨j, x⟩
  cases h
  rfl

lemma sigmaValue_transport_mk {ι : Type u} {A : ι → Type u}
    (x : Σ j, A j) {i : ι} (h : x.1 = i) : (⟨i, h ▸ x.2⟩ : Σ j, A j) = x := by
  rcases x with ⟨j, x⟩
  cases h
  rfl

/-- 概要：同じラベルに値を持つ元の全図式を、その元の成分へ戻す。
方針：ラベルの等式で第二成分を輸送する。
規約：元の全図式の全単体と自然性を保持する。
使われ方：内ホーンの成分内の充填。 -/
def sigmaSSetFactor {ι : Type u} {C : ι → SSet.{u}} {K : SSet.{u}}
    (a : K ⟶ sigmaSSet C) (i : ι)
    (h : ∀ (n : SimplexCategoryᵒᵖ) (k : K.obj n), (a.app n k).1 = i) : K ⟶ C i where
  app n := ↾fun k ↦ h n k ▸ (a.app n k).2
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro k
    have ha : a.app m (K.map α k) =
        ⟨(a.app n k).1, (C (a.app n k).1).map α (a.app n k).2⟩ :=
      ConcreteCategory.congr_hom (C := Type u) (a.naturality α) k
    exact (sigmaValue_transport_congr ha (h m (K.map α k)) (h n k)).trans
      (sigmaValue_transport_map C α (a.app n k) (h n k))

/-- 概要：元の成分へ戻して再び含めると元の全図式。
方針：輸送した依存対を元の単体へ戻す。
規約：全射の厳密な等式。
使われ方：成分内のホーン充填から元の境界を回収する。 -/
lemma sigmaSSetFactor_inclusion {ι : Type u} {C : ι → SSet.{u}} {K : SSet.{u}}
    (a : K ⟶ sigmaSSet C) (i : ι)
    (h : ∀ (n : SimplexCategoryᵒᵖ) (k : K.obj n), (a.app n k).1 = i) :
    sigmaSSetFactor a i h ≫ sigmaSSetInclusion C i = a := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro k
  exact sigmaValue_transport_mk (a.app n k) (h n k)

/-- 概要：小さい quasicategory の族の元の直和も quasicategory。
方針：定値ラベルのホーン充填から一定のラベルを取り、その一成分で元のホーンを埋める。
規約：任意の小さい添字の族を扱う。
使われ方：積の底の前層圏の presentable 性。 -/
instance sigmaSSet_quasicategory {ι : Type u} (C : ι → SSet.{u}) [∀ i, Quasicategory (C i)] :
    Quasicategory (sigmaSSet C) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.constant_isQuasicategory ι
  constructor
  intro n k a h0 hn
  obtain ⟨b, hb⟩ := Quasicategory.hornFilling h0 hn (a ≫ sigmaSSetProjection C)
  obtain ⟨i, rfl⟩ := SSet.yonedaEquiv.symm.surjective b
  have htag : ∀ (d : SimplexCategoryᵒᵖ) (x : (Λ[n + 2, k] : SSet.{u}).obj d),
      (a.app d x).1 = i := by
    intro d x
    exact congrArg (fun q ↦ q.app d x) hb
  obtain ⟨s, hs⟩ := Quasicategory.hornFilling h0 hn (sigmaSSetFactor a i htag)
  refine ⟨s ≫ sigmaSSetInclusion C i, ?_⟩
  have h := congrArg (fun q ↦ q ≫ sigmaSSetInclusion C i) hs
  simpa only [Category.assoc, sigmaSSetFactor_inclusion] using h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
