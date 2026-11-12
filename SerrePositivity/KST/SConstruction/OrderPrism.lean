module
public import SerrePositivity.KST.SConstruction.ArTimeCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PrismLastContraction

/-! # 点ごとに順序づけられた順序写像の prism
概要：点ごとに f≤g となる順序写像から nerve 上の実際の自然変換を作る。
方針：二点鎖と添字の積の順序写像を各鎖に適用する。
規約：時刻は第一因子。使われ方：McCarthy の λ→μ の添字の変換。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：点ごとに順序づけられた二つの順序写像をつなぐ順序写像。
方針：時刻零で f、時刻一で g を取る。
規約：順序は前順序でよい。使われ方：nerve の prism の定義。 -/
def orderPrismOrder {A B : Type u} [Preorder A] [Preorder B]
    (f g : A →o B) (h : ∀ a, f a ≤ g a) : Fin 2 × A →o B where
  toFun x := if x.1 = 0 then f x.2 else g x.2
  monotone' {x y} hxy := by
    dsimp only
    split_ifs with hx hy hy
    · exact f.monotone hxy.2
    · exact (f.monotone hxy.2).trans (h y.2)
    · have hx' : x.1.val = 1 := by have := x.1.isLt; omega
      have hy' := Fin.le_iff_val_le_val.mp hxy.1
      simp only [hy, Fin.val_zero] at hy'
      omega
    · exact g.monotone hxy.2

/-- 概要：点ごとに f≤g となる順序写像から nerve 上の prism を作る。
方針：各単体の時刻列と添字列を積にして順序写像を適用する。
規約：始域と標的の同じ宇宙で構成する。使われ方：Ar の添字の coherent な変換。 -/
def orderPrism {A B : Type u} [Preorder A] [Preorder B]
    (f g : A →o B) (h : ∀ a, f a ≤ g a) :
    (Δ[1] : SSet.{u}) ⊗ nerve A ⟶ nerve B where
  app d := ↾fun s => ((orderPrismOrder f g h).comp
    ((stdSimplex.objEquiv s.1).toOrderHom.prod
      ⟨s.2.obj, fun _ _ hij => leOfHom (s.2.map (homOfLE hij))⟩)).toFunctor
  naturality {_d _e} α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    funext j
    rfl

/-- 概要：順序 prism の始点は f の nerve。
方針：時刻零を各鎖の各頂点で計算する。
規約：厳密な射の等号。使われ方：λ 側の添字の照合。 -/
lemma orderPrism_zero {A B : Type u} [Preorder A] [Preorder B]
    (f g : A →o B) (h : ∀ a, f a ≤ g a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (nerve A) ≫ orderPrism f g h = nerveMap f.toFunctor := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext j
  rfl

/-- 概要：順序 prism の終点は g の nerve。
方針：時刻一を各鎖の各頂点で計算する。
規約：厳密な射の等号。使われ方：μ 側の添字の照合。 -/
lemma orderPrism_one {A B : Type u} [Preorder A] [Preorder B]
    (f g : A →o B) (h : ∀ a, f a ≤ g a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (nerve A) ≫ orderPrism f g h = nerveMap g.toFunctor := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext j
  rfl

/-- 概要：順序 prism は添字の前合成と厳密に両立する。
方針：各鎖の各頂点で合成を計算する。
規約：順序写像 k は任意。使われ方：面・退化との両立。 -/
lemma orderPrism_pre {A B D : Type u} [Preorder A] [Preorder B] [Preorder D]
    (f g : A →o B) (h : ∀ a, f a ≤ g a) (k : D →o A) :
    (Δ[1] ◁ nerveMap k.toFunctor) ≫ orderPrism f g h =
      orderPrism (f.comp k) (g.comp k) (fun d => h (k d)) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext j
  rfl

/-- 概要：順序 prism は標的の順序写像への後合成と両立する。
方針：時刻の二つの場合を各鎖の各頂点で計算する。
規約：順序写像 k は任意。使われ方：Ar と元の圏の図式を結ぶ変換。 -/
lemma orderPrism_post {A B D : Type u} [Preorder A] [Preorder B] [Preorder D]
    (f g : A →o B) (h : ∀ a, f a ≤ g a) (k : B →o D) :
    orderPrism f g h ≫ nerveMap k.toFunctor =
      orderPrism (k.comp f) (k.comp g) (fun a => k.monotone (h a)) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext j
  change k (if _ then _ else _) = if _ then _ else _
  split_ifs <;> rfl

/-- 概要：二つの順序写像が同じなら prism は時刻に依存しない。
方針：時刻の二つの分岐が同じ値を取る。
規約：順序条件の証明には依存しない。使われ方：McCarthy の零時刻の正規化。 -/
lemma orderPrism_refl {A B : Type u} [Preorder A] [Preorder B]
    (f : A →o B) (h : ∀ a, f a ≤ f a) :
    orderPrism f f h = CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) (nerve A) ≫
      nerveMap f.toFunctor := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext j
  change (if _ then _ else _) = _
  split_ifs <;> rfl

/-- 概要：始点と終点の順序写像が等しい prism は一定。
方針：終点の写像を等号で置き換え、定値 prism の式を使う。
規約：順序条件の証明を持つ依存型の置換を明示する。使われ方：McCarthy の零時刻の式。 -/
lemma orderPrism_of_eq {A B : Type u} [Preorder A] [Preorder B]
    (f g : A →o B) (h : ∀ a, f a ≤ g a) (hg : g = f) :
    orderPrism f g h = CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) (nerve A) ≫
      nerveMap f.toFunctor := by
  subst g
  exact orderPrism_refl f h

end SerrePositivity.KST.SConstruction
