module

public import SerrePositivity.KST.Comparison.PartialSections

/-!
# 元の全空間から部分切断の対象への写像

概要：A→B が単射のとき、Z→A の全空間を部分切断の対象へ送る。
方針：基底変換の第一射影を随伴で転置し、単射性から部分切断の条件を示す。
規約：Segal 1974 Lemma 1.7 の厳密化の補助。制限の引き戻し性は別に証明する。
使われ方：trivial fibration の延長の元の全空間への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：元の全空間の恒等写像を右随伴へ転置した写像。
方針：Z×_B A→Z の第一射影を使う。
規約：Z の B への構造射は Z→A→B の合成。
使われ方：部分切断の対象への写像の第一成分。
-/
def partialSectionLiftMap {Z A B : SSet.{u}} (p : A ⟶ B) (q : Z ⟶ A) :
    Over.mk (q ≫ p) ⟶ (sliceFiberFunctor p).rightAdjoint.obj Z :=
  (Adjunction.ofIsLeftAdjoint (sliceFiberFunctor p)).homEquiv _ _ (pullback.fst (q ≫ p) p)

/--
概要：単射に沿う転置は、元の射との合成で恒等切断の条件を満たす。
方針：随伴の逆で両辺を戻し、単射の引き戻しの二つの射影の整合を使う。
規約：A→B の単射性をここで使う。
使われ方：部分切断の引き戻しへの持ち上げ。
-/
theorem partialSectionLiftMap_comp {Z A B : SSet.{u}} (p : A ⟶ B) [Mono p] (q : Z ⟶ A) :
    partialSectionLiftMap p q ≫ (sliceFiberFunctor p).rightAdjoint.map q =
      (Over.homMk (q ≫ p) : Over.mk (q ≫ p) ⟶ Over.mk (𝟙 B)) ≫ partialSectionUnit p := by
  let F := sliceFiberFunctor p
  let adj := Adjunction.ofIsLeftAdjoint F
  have h₁ : (adj.homEquiv _ _).symm (partialSectionLiftMap p q) =
      pullback.fst (q ≫ p) p := (adj.homEquiv _ _).symm_apply_apply _
  have h₂ : (adj.homEquiv _ _).symm (partialSectionUnit p) =
      pullback.snd (𝟙 B) p := (adj.homEquiv _ _).symm_apply_apply _
  apply (adj.homEquiv (Over.mk (q ≫ p)) A).symm.injective
  rw [adj.homEquiv_naturality_right_symm, adj.homEquiv_naturality_left_symm, h₁, h₂]
  have hS : F.map (Over.homMk (q ≫ p) : Over.mk (q ≫ p) ⟶ Over.mk (𝟙 B)) ≫
      pullback.snd (𝟙 B) p = pullback.snd (q ≫ p) p :=
    sliceFiberFunctor_map_snd p (Over.homMk (q ≫ p) : Over.mk (q ≫ p) ⟶ Over.mk (𝟙 B))
  rw [hS]
  apply (cancel_mono p).mp
  rw [Category.assoc]
  exact pullback.condition

/--
概要：元の全空間を部分切断の対象へ送る、B 上の写像。
方針：転置した第一射影と終対象への射から、部分切断の引き戻しへ持ち上げる。
規約：A→B が単射であることを要求する。
使われ方：延長の制限を元の射と比較する。
-/
def partialSectionInclusionOver {Z A B : SSet.{u}} (p : A ⟶ B) [Mono p] (q : Z ⟶ A) :
    Over.mk (q ≫ p) ⟶ partialSectionObject p q :=
  pullback.lift (partialSectionLiftMap p q) (Over.homMk (q ≫ p)) (partialSectionLiftMap_comp p q)

/--
概要：元の全空間から部分切断の全空間への基礎写像。
方針：B 上の包含の基礎射を取る。
規約：包含という名前は制限の比較の向きを表し、ここでは単射性をまだ主張しない。
使われ方：延長の引き戻し正方形の上辺。
-/
def partialSectionInclusion {Z A B : SSet.{u}} (p : A ⟶ B) [Mono p] (q : Z ⟶ A) :
    Z ⟶ (partialSectionObject p q).left :=
  (partialSectionInclusionOver p q).left

/--
概要：部分切断の包含は B への構造射と可換である。
方針：スライス内の射であることを忘れる。
規約：元の構造射は q と p の合成。
使われ方：延長の制限の正方形の可換性。
-/
@[reassoc] theorem partialSectionInclusion_base {Z A B : SSet.{u}}
    (p : A ⟶ B) [Mono p] (q : Z ⟶ A) :
    partialSectionInclusion p q ≫ (partialSectionObject p q).hom = q ≫ p :=
  Over.w (partialSectionInclusionOver p q)

/--
概要：部分切断の包含の第一射影は、転置した第一射影である。
方針：引き戻しへの持ち上げの計算則を使う。
規約：等式は B 上の射として成立する。
使われ方：制限の引き戻し性の普遍性。
-/
@[reassoc] theorem partialSectionInclusionOver_fst {Z A B : SSet.{u}}
    (p : A ⟶ B) [Mono p] (q : Z ⟶ A) :
    partialSectionInclusionOver p q ≫
      pullback.fst ((sliceFiberFunctor p).rightAdjoint.map q) (partialSectionUnit p) =
        partialSectionLiftMap p q := pullback.lift_fst ..

end SerrePositivity.KST.Comparison
