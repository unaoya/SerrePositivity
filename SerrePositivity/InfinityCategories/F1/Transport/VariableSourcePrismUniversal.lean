module

public import SerrePositivity.InfinityCategories.F1.Transport.VariableSourcePrismBaseChange

/-!
概要：動く初期値の全 lift prism 空間の任意の族に対する普遍性。
方針：指定した prism を curry し、初期値データの底変換の等式を使う。
規約：パラメーター上の全空間の射を厳密に回収する。
使われ方：端点制限の相対ホーン充填を全 lift 空間へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：指定した始点と底を持つ prism を動く初期値の全 lift 空間へ戻す。
方針：データの底変換と実際の prism の相対制限を比較する。
規約：初期値はパラメーターとともに動いてよい。
使われ方：同時の端点制限の充填の構成。 -/
def prismLiftSpaceLift {E B K L M : SSet.{u}} (p : E ⟶ B) (v : K ⊗ L ⟶ E)
    (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B) (hv : v ≫ p = prismEndpoint 0 _ ≫ δ)
    (g : M ⟶ L) (H : Δ[1] ⊗ (K ⊗ M) ⟶ E)
    (h₀ : prismEndpoint 0 _ ≫ H = (K ◁ g) ≫ v)
    (hp : H ≫ p = (Δ[1] ◁ (K ◁ g)) ≫ δ) :
    M ⟶ prismLiftSpace p K (prismLiftData p v δ hv) :=
  pullback.lift (curry ((α_ Δ[1] K M).hom ≫ H)) g (by
    symm
    rw [prismLiftData_precomp]
    exact prismLiftData_eq_of_prism p _ _ _ H h₀ hp)

/-- 概要：prism を lift 空間へ戻すと元のパラメーターを厳密に回収する。
方針：引き戻しの第二射影の公式。
規約：全次数での射の等式。
使われ方：相対充填の底のパラメーター条件。 -/
lemma prismLiftSpaceLift_projection {E B K L M : SSet.{u}} (p : E ⟶ B) (v : K ⊗ L ⟶ E)
    (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B) (hv : v ≫ p = prismEndpoint 0 _ ≫ δ)
    (g : M ⟶ L) (H : Δ[1] ⊗ (K ⊗ M) ⟶ E)
    (h₀ : prismEndpoint 0 _ ≫ H = (K ◁ g) ≫ v)
    (hp : H ≫ p = (Δ[1] ◁ (K ◁ g)) ≫ δ) :
    prismLiftSpaceLift p v δ hv g H h₀ hp ≫
      prismLiftSpaceProjection p K (prismLiftData p v δ hv) = g := pullback.lift_snd _ _ _

/-- 概要：prism を lift 空間へ戻すと元の curry を厳密に回収する。
方針：引き戻しの第一射影の公式。
規約：初期値の動きを保持する。
使われ方：相対充填の一致を全 prism で検査する。 -/
lemma prismLiftSpaceLift_curry {E B K L M : SSet.{u}} (p : E ⟶ B) (v : K ⊗ L ⟶ E)
    (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B) (hv : v ≫ p = prismEndpoint 0 _ ≫ δ)
    (g : M ⟶ L) (H : Δ[1] ⊗ (K ⊗ M) ⟶ E)
    (h₀ : prismEndpoint 0 _ ≫ H = (K ◁ g) ≫ v)
    (hp : H ≫ p = (Δ[1] ◁ (K ◁ g)) ≫ δ) :
    prismLiftSpaceLift p v δ hv g H h₀ hp ≫
      prismLiftSpaceCurry p K (prismLiftData p v δ hv) =
        curry ((α_ Δ[1] K M).hom ≫ H) := pullback.lift_fst _ _ _

/-- 概要：動く初期値の lift 空間への族はパラメーターと全 prism で一意に決まる。
方針：引き戻しの二射影の一意性を使う。
規約：端点だけの一致ではなく prism の curry の一致を要求する。
使われ方：既定のホーン上での lift の厳密な一致。 -/
lemma prismLiftSpace_hom_ext {E B K L M : SSet.{u}} (p : E ⟶ B)
    (d : L ⟶ (transportPrismRelativeHom p K).pt) {f g : M ⟶ prismLiftSpace p K d}
    (hH : f ≫ prismLiftSpaceCurry p K d = g ≫ prismLiftSpaceCurry p K d)
    (hg : f ≫ prismLiftSpaceProjection p K d = g ≫ prismLiftSpaceProjection p K d) :
    f = g := pullback.hom_ext hH hg

/-- 概要：全 lift 空間へ戻した族を評価すると元の prism。
方針：curry の回収と uncurry の自然性を使う。
規約：初期値も動く任意の族を扱う。
使われ方：充填の終点条件を実際の終点射へ戻す。 -/
lemma prismLiftSpaceLift_prism {E B K L M : SSet.{u}} (p : E ⟶ B) (v : K ⊗ L ⟶ E)
    (δ : Δ[1] ⊗ (K ⊗ L) ⟶ B) (hv : v ≫ p = prismEndpoint 0 _ ≫ δ)
    (g : M ⟶ L) (H : Δ[1] ⊗ (K ⊗ M) ⟶ E)
    (h₀ : prismEndpoint 0 _ ≫ H = (K ◁ g) ≫ v)
    (hp : H ≫ p = (Δ[1] ◁ (K ◁ g)) ≫ δ) :
    (Δ[1] ◁ (K ◁ prismLiftSpaceLift p v δ hv g H h₀ hp)) ≫
      prismLiftSpacePrism p K (prismLiftData p v δ hv) = H := by
  calc
    _ = (α_ Δ[1] K M).inv ≫ uncurry
        (prismLiftSpaceLift p v δ hv g H h₀ hp ≫
          prismLiftSpaceCurry p K (prismLiftData p v δ hv)) := by
      rw [uncurry_natural_left]
      rfl
    _ = _ := by rw [prismLiftSpaceLift_curry, uncurry_curry, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories
