module

public import SerrePositivity.KST.LocalizingInvariants.CoconeFamilyTranspose
public import SerrePositivity.InfinityCategories.F2.Presentable.FlipConstantFunctorHom

/-!
概要：元の二重内部 Hom 交換の反転と図式形状制限との厳密自然性。
方針：全単体での二度の交換を元の関手の自然性へ戻し、既存の第二変数自然性と結ぶ。
規約：比較辺・図式・パラメータを選び直さない。
使われ方：実 pullback 族の cospan 境界と終端列を全族で照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の二重内部 Hom の二度の交換は、全単体写像として恒等。 -/
@[reassoc]
lemma spanInternalHomSwap_swap (A B X : SSet.{u}) :
    (internalHomSwapIso A B X).hom ≫ (internalHomSwapIso B A X).hom = 𝟙 _ := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro e α
  apply ConcreteCategory.hom_ext
  intro a
  apply CategoryTheory.Functor.functorHom_ext
  intro t β
  apply ConcreteCategory.hom_ext
  intro b
  change (F.app t ((α ≫ β) ≫ 𝟙 t) (A.map β a)).app t (𝟙 t) (B.map (𝟙 t) b) =
    (F.app e α a).app t β b
  rw [Category.comp_id, CategoryTheory.Functor.map_id_apply]
  have hn := ConcreteCategory.congr_hom (F.naturality β α) a
  have he := congrArg (fun G : ((ihom B).obj X).obj t => G.app t (𝟙 t) b) hn
  change (F.app t (α ≫ β) (A.map β a)).app t (𝟙 t) b =
    (F.app e α a).app t (β ≫ 𝟙 t) b at he
  simpa only [Category.comp_id] using he

/-- 形状側での制限も、同じ元の交換と全単体で可換する。 -/
lemma spanInternalHomSwap_pre_first {A A' B X : SSet.{u}} (j : A' ⟶ A) :
    (pre j).app ((ihom B).obj X) ≫ (internalHomSwapIso A' B X).hom =
      (internalHomSwapIso A B X).hom ≫ (ihom B).map ((pre j).app X) := by
  have h := congrArg (fun f => (internalHomSwapIso A B X).hom ≫ f)
    (internalHomSwapIso_pre (A := B) (X := X) j)
  have hh := congrArg (fun f => f ≫ (internalHomSwapIso A' B X).hom) h
  simpa only [Category.assoc, spanInternalHomSwap_swap_assoc,
    spanInternalHomSwap_swap, Category.comp_id] using hh.symm

/-- 同じ射の転置は、標的の後合成とも厳密に可換。 -/
lemma spanInternalHomFlip_post {A B X Y : SSet.{u}} (f : X ⟶ Y)
    (g : A ⟶ (ihom B).obj X) :
    internalHomFlipHomEquiv A B Y (g ≫ (ihom B).map f) =
      internalHomFlipHomEquiv A B X g ≫ (ihom A).map f := by
  apply uncurry_injective
  change uncurry (curry ((β_ A B).hom ≫ uncurry (g ≫ (ihom B).map f))) =
    uncurry (curry ((β_ A B).hom ≫ uncurry g) ≫ (ihom A).map f)
  simp only [uncurry_natural_right, uncurry_curry, Category.assoc]

/-- 全図式を、元のパラメータごとの全形状図式へ交換する。 -/
def spanDiagramFamilyTranspose {A L P X : SSet.{u}}
    (Q : A ⟶ (ihom L).obj ((ihom P).obj X)) :
    P ⟶ (ihom L).obj ((ihom A).obj X) :=
  internalHomFlipHomEquiv L P ((ihom A).obj X)
    (internalHomFlipHomEquiv A L ((ihom P).obj X) Q ≫ (internalHomSwapIso A P X).hom)

/-- 同じ三変数の転置を二度行うと、元の全単体写像へ厳密に戻る。 -/
lemma spanDiagramFamilyTranspose_transpose {A L P X : SSet.{u}}
    (Q : A ⟶ (ihom L).obj ((ihom P).obj X)) :
    spanDiagramFamilyTranspose (spanDiagramFamilyTranspose Q) = Q := by
  change internalHomFlipHomEquiv L A ((ihom P).obj X)
    (internalHomFlipHomEquiv P L ((ihom A).obj X) (spanDiagramFamilyTranspose Q) ≫
      (internalHomSwapIso P A X).hom) = Q
  have ht : internalHomFlipHomEquiv P L ((ihom A).obj X) (spanDiagramFamilyTranspose Q) =
      internalHomFlipHomEquiv A L ((ihom P).obj X) Q ≫ (internalHomSwapIso A P X).hom :=
    (internalHomFlipHomEquiv L P ((ihom A).obj X)).symm_apply_apply _
  rw [ht, Category.assoc, spanInternalHomSwap_swap, Category.comp_id]
  exact (internalHomFlipHomEquiv A L ((ihom P).obj X)).symm_apply_apply Q

/-- 中央の図式形状の制限も、同じ全転置と厳密に可換する。 -/
lemma spanDiagramFamilyTranspose_pre_diagram {A L L' P X : SSet.{u}} (j : L' ⟶ L)
    (Q : A ⟶ (ihom L).obj ((ihom P).obj X)) :
    spanDiagramFamilyTranspose (Q ≫ (pre j).app ((ihom P).obj X)) =
      spanDiagramFamilyTranspose Q ≫ (pre j).app ((ihom A).obj X) := by
  rw [spanDiagramFamilyTranspose, internalHomFlipHomEquiv_pre_app,
    Category.assoc, internalHomFlipHomEquiv_pre]
  rfl

/-- 同じ全図式族の交換は、元の形状の全制限を保持する。 -/
lemma spanDiagramFamilyTranspose_pre_shape {A A' L P X : SSet.{u}}
    (j : A' ⟶ A) (Q : A ⟶ (ihom L).obj ((ihom P).obj X)) :
    spanDiagramFamilyTranspose (j ≫ Q) =
      spanDiagramFamilyTranspose Q ≫ (ihom L).map ((pre j).app X) := by
  rw [spanDiagramFamilyTranspose, internalHomFlipHomEquiv_pre j Q,
    Category.assoc, spanInternalHomSwap_pre_first (B := P) (X := X) j,
    ← Category.assoc]
  exact spanInternalHomFlip_post ((pre j).app X)
    (internalHomFlipHomEquiv A L ((ihom P).obj X) Q ≫ (internalHomSwapIso A P X).hom)

/-- 元のパラメータの制限は、交換後の全図式族の同じ制限になる。 -/
lemma spanDiagramFamilyTranspose_pre_parameter {A L P P' X : SSet.{u}}
    (j : P' ⟶ P) (Q : A ⟶ (ihom L).obj ((ihom P).obj X)) :
    spanDiagramFamilyTranspose (Q ≫ (ihom L).map ((pre j).app X)) =
      j ≫ spanDiagramFamilyTranspose Q := by
  rw [spanDiagramFamilyTranspose, spanInternalHomFlip_post ((pre j).app X) Q,
    Category.assoc, internalHomSwapIso_pre (A := A) (X := X) j,
    ← Category.assoc, internalHomFlipHomEquiv_pre_app j]
  rfl

/-- 元の一つの図式を全パラメータで定値にした場合は、同じ全関手頂点への定値族。 -/
lemma spanDiagramFamilyTranspose_post_constant {A L X : SSet.{u}} (P : SSet.{u})
    (Q : A ⟶ (ihom L).obj X) :
    spanDiagramFamilyTranspose (Q ≫ (ihom L).map (constantFunctorMap P X)) =
      SSet.const (functorVertex (internalHomFlipHomEquiv A L X Q)) := by
  rw [spanDiagramFamilyTranspose, spanInternalHomFlip_post (constantFunctorMap P X) Q,
    Category.assoc, F2.Presentable.swap_postcompose_constant,
    F2.Presentable.flip_postcompose_constant]

/-- 定値関手族の各評価は、元の同じ対象を全単体で回収する。 -/
lemma spanConstantFunctorMap_evaluate (P X : SSet.{u}) (p : P _⦋0⦌) :
    constantFunctorMap P X ≫ evaluateFunctorAt p = 𝟙 X := by
  rw [constantFunctorMap, curry_evaluateFunctorAt_vertex, CartesianMonoidalCategory.lift_snd]

end SerrePositivity.KST.LocalizingInvariants
