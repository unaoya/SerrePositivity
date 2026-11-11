module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomSquare

/-!
概要：prism 上の図式のホモトピーを h Fun の正方形に転置する。
方針：二つの時間とパラメータを並べ替えて curry し、四辺を厳密に回収する。
規約：元の prism の時間が正方形の横軸、図式のホモトピーの時間が縦軸。
使われ方：相対 join の厳密化で二つの補正正方形を比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：パラメータ・prism 時間・補正時間の座標を並べ替える。
方針：各次数の直積の成分を移す。
規約：補正時間は第二の区間。
使われ方：補正ホモトピーを関手正方形へ curry する。 -/
def prismSquareReorder (K : SSet.{u}) :
    K ⊗ ((Δ[1] : SSet.{u}) ⊗ Δ[1]) ⟶ ((Δ[1] : SSet.{u}) ⊗ K) ⊗ Δ[1] where
  app _ := ↾fun z ↦ ((z.2.1, z.1), z.2.2)
  naturality {_ _} _ := rfl

/-- 概要：prism 上の図式の族を関手単体集合の正方形にする。
方針：二つの区間以外のパラメータを curry する。
規約：ホモトピーの端点条件は不要。
使われ方：四辺の raw な計算。 -/
def prismSquare {K D : SSet.{u}} (H : ((Δ[1] : SSet.{u}) ⊗ K) ⊗ Δ[1] ⟶ D) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom K).obj D :=
  curry (prismSquareReorder K ≫ H)

/-- 概要：転置正方形の下辺は元の族の始端。
方針：uncurry して三座標で評価する。
規約：端点条件のない raw な式。
使われ方：正方形の下辺の認証。 -/
lemma prismSquare_zero {K D : SSet.{u}}
    (H : ((Δ[1] : SSet.{u}) ⊗ K) ⊗ Δ[1] ⟶ D) :
    SSet.ι₀ ≫ prismSquare H = curry ((β_ K (Δ[1] : SSet.{u})).hom ≫ SSet.ι₀ ≫ H) := by
  apply uncurry_injective
  rw [uncurry_natural_left, prismSquare, uncurry_curry, uncurry_curry]
  rfl

/-- 概要：転置正方形の上辺は元の族の終端。
方針：uncurry して三座標で評価する。
規約：端点条件のない raw な式。
使われ方：正方形の上辺の認証。 -/
lemma prismSquare_one {K D : SSet.{u}}
    (H : ((Δ[1] : SSet.{u}) ⊗ K) ⊗ Δ[1] ⟶ D) :
    SSet.ι₁ ≫ prismSquare H = curry ((β_ K (Δ[1] : SSet.{u})).hom ≫ SSet.ι₁ ≫ H) := by
  apply uncurry_injective
  rw [uncurry_natural_left, prismSquare, uncurry_curry, uncurry_curry]
  rfl

/-- 概要：転置正方形の左右の辺は prism の端点上の補正ホモトピー。
方針：uncurry して端点と三座標の並びを計算する。
規約：i は prism 時間の端点。
使われ方：同じ端点補正を共有する二つの正方形の比較。 -/
lemma prismSquare_endpoint {K D : SSet.{u}}
    (H : ((Δ[1] : SSet.{u}) ⊗ K) ⊗ Δ[1] ⟶ D) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (Δ[1] : SSet.{u}) ≫ prismSquare H =
      curry ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i K ▷ (Δ[1] : SSet.{u})) ≫ H) := by
  apply uncurry_injective
  rw [uncurry_natural_left, prismSquare, uncurry_curry, uncurry_curry]
  rfl

/-- 概要：二つの指定自然変換を結ぶ prism ホモトピーの左端。
方針：prism の零端で制限して両端を計算する。
規約：入力 H の時間は第二因子。
使われ方：関手正方形の左辺。 -/
def prismHomotopyLeft {K D : SSet.{u}} {U₀ U₁ V₀ V₁ : K ⟶ D}
    (f : SSet.Homotopy U₀ U₁) (g : SSet.Homotopy V₀ V₁)
    (H : SSet.Homotopy ((β_ (Δ[1] : SSet.{u}) K).hom ≫ f.h)
      ((β_ (Δ[1] : SSet.{u}) K).hom ≫ g.h)) : SSet.Homotopy U₀ V₀ where
  h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ▷ (Δ[1] : SSet.{u})) ≫ H.h
  h₀ := by
    rw [SSet.ι₀_comp_assoc, H.h₀, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding, f.h₀]
    rfl
  h₁ := by
    rw [SSet.ι₁_comp_assoc, H.h₁, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding, g.h₀]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：二つの指定自然変換を結ぶ prism ホモトピーの右端。
方針：prism の一端で制限する。
規約：入力 H の時間は第二因子。
使われ方：関手正方形の右辺。 -/
def prismHomotopyRight {K D : SSet.{u}} {U₀ U₁ V₀ V₁ : K ⟶ D}
    (f : SSet.Homotopy U₀ U₁) (g : SSet.Homotopy V₀ V₁)
    (H : SSet.Homotopy ((β_ (Δ[1] : SSet.{u}) K).hom ≫ f.h)
      ((β_ (Δ[1] : SSet.{u}) K).hom ≫ g.h)) : SSet.Homotopy U₁ V₁ where
  h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ▷ (Δ[1] : SSet.{u})) ≫ H.h
  h₀ := by
    rw [SSet.ι₀_comp_assoc, H.h₀, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding, f.h₁]
    rfl
  h₁ := by
    rw [SSet.ι₁_comp_assoc, H.h₁, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding, g.h₁]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：prism ホモトピーは四辺を指定した関手正方形を与える。
方針：転置正方形の四辺の計算を入力ホモトピーの端点条件に適用する。
規約：辺の代表を変更しない。
使われ方：二つの補正経路の h Fun 内での比較。 -/
def prismHomotopySquare {K D : SSet.{u}} {U₀ U₁ V₀ V₁ : K ⟶ D}
    (f : SSet.Homotopy U₀ U₁) (g : SSet.Homotopy V₀ V₁)
    (H : SSet.Homotopy ((β_ (Δ[1] : SSet.{u}) K).hom ≫ f.h)
      ((β_ (Δ[1] : SSet.{u}) K).hom ≫ g.h)) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomSquare f g (prismHomotopyLeft f g H) (prismHomotopyRight f g H) where
  diagram := prismSquare H.h
  bottom := by
    rw [prismSquare_zero, H.h₀, ← Category.assoc,
      SymmetricCategory.symmetry, Category.id_comp]
  top := by
    rw [prismSquare_one, H.h₁, ← Category.assoc,
      SymmetricCategory.symmetry, Category.id_comp]
  left := prismSquare_endpoint H.h 0
  right := prismSquare_endpoint H.h 1

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
