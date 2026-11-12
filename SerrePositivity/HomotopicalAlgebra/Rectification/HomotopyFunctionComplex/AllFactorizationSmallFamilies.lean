module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.AllFactorizationCoherentSquare
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NerveLargeSampling
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.AnchoredChainFiniteTest

/-!
# 中断した任意モデル源への一般化：AllFactorizationSmallFamilies

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Original-universe whole finite families of the old all-factorization square。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0058][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0058
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Original-universe whole finite families of the old all-factorization square
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open AllFactorizationCoherentSquare

namespace SerrePositivity.HomotopyFunctionComplex.AllFactorizationSmallFamilies
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (X : FramedResolution C) (Y V : ResolutionObject C) (f : X.inner.base ⟶ Y.base) (g : Y ⟶ V)

abbrev smallParameter (m r : ℕ) := AnchoredChainFiniteTest.smallParameter.{v} m r

omit [ModelCategory SSet.{v}] in
def test {Y V : ResolutionObject C} (g : Y ⟶ V) {m : ℕ} (d : AnchoredChain g m) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} (smallParameter.{v} m r) ⟶ AnchoredChainFiniteTest.parameter g r :=
  (UniverseLift.stableIso.{v, u} (smallParameter.{v} m r)).hom ≫
    AnchoredChainFiniteTest.test g d r

omit [ModelCategory SSet.{v}] in
lemma test_reindex {Y V : ResolutionObject C} (g : Y ⟶ V) {m n : ℕ} (d : AnchoredChain g m)
    (ψ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (SSet.stdSimplex.map ψ ▷ SSet.stdSimplex.obj (SimplexCategory.mk r)) ≫
      test g d r = test g (d.reindex ψ.toOrderHom) r := by
  unfold test
  rw [← Category.assoc, UniverseLift.stableIso_naturality, Category.assoc,
    AnchoredChainFiniteTest.test_reindex]

omit [ModelCategory SSet.{v}] in
lemma test_operator {Y V : ResolutionObject C} (g : Y ⟶ V) {m r s : ℕ} (d : AnchoredChain g m)
    (θ : SimplexCategory.mk r ⟶ SimplexCategory.mk s) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (SSet.stdSimplex.obj (SimplexCategory.mk m) ◁ SSet.stdSimplex.map θ) ≫
      test g d s = test g d r ≫ AnchoredChain.simplicial g ◁ SSet.stdSimplex.map θ := by
  unfold test
  rw [← Category.assoc, UniverseLift.stableIso_naturality, Category.assoc,
    AnchoredChainFiniteTest.test_operator, Category.assoc]

/-- Keep the same whole global triangle and the full finite factor and triangle parameters. -/
def family (side : Bool) {m n : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) :
    smallParameter.{v} m 2 ⊗ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶
      (values hcof X Y V f g).obj (c.obj (Fin.last n)) :=
  NerveLargeSampling.family (values hcof X Y V f g) (triangle hcof hfib X Y V f g side)
    (test g d 2) c

abbrev faceFamily (side : Bool) (k : Fin 3) {m n : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) :=
  NerveLargeSampling.family (values hcof X Y V f g) (edge hcof hfib X Y V f g side k)
    (test g d 1) c

lemma external_naturality (side : Bool) {m n l : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) (θ : SimplexCategory.mk l ⟶ SimplexCategory.mk n) :
    smallParameter.{v} m 2 ◁ SSet.stdSimplex.map θ ≫ family hcof hfib X Y V f g side d c =
    family hcof hfib X Y V f g side d ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
      (values hcof X Y V f g).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last l))))) :=
  NerveLargeSampling.family_naturality _ _ _ c θ

lemma factor_naturality (side : Bool) {m n l : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) (ψ : SimplexCategory.mk l ⟶ SimplexCategory.mk m) :
    ((SSet.stdSimplex.map ψ ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2)) ▷
      SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ family hcof hfib X Y V f g side d c =
    family hcof hfib X Y V f g side (d.reindex ψ.toOrderHom) c := by
  apply (NerveLargeSampling.family_precomp (values hcof X Y V f g)
    (triangle hcof hfib X Y V f g side) (test g d 2)
    (SSet.stdSimplex.map ψ ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2)) c).symm.trans
  exact congrArg (fun k => NerveLargeSampling.family _ _ k c)
    (test_reindex g d ψ 2)

lemma family_face (side : Bool) (k : Fin 3) {m n : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) :
    ((SSet.stdSimplex.obj (SimplexCategory.mk m) ◁ SSet.stdSimplex.δ k) ▷
      SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ family hcof hfib X Y V f g side d c =
    faceFamily hcof hfib X Y V f g side k d c := by
  apply (NerveLargeSampling.family_precomp (values hcof X Y V f g)
    (triangle hcof hfib X Y V f g side) (test g d 2)
    (SSet.stdSimplex.obj (SimplexCategory.mk m) ◁ SSet.stdSimplex.δ k) c).symm.trans
  apply (congrArg (fun l => NerveLargeSampling.family _ _ l c)
    (test_operator g d (SimplexCategory.δ k))).trans
  exact (NerveLargeSampling.family_restrict _ _ _ _ c).symm

lemma shared_diagonal {m n : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) :
    faceFamily hcof hfib X Y V f g true 1 d c = faceFamily hcof hfib X Y V f g false 1 d c :=
  congrArg (fun a => NerveLargeSampling.family (values hcof X Y V f g) a
    (test g d 1) c) (AllFactorizationCoherentSquare.shared_diagonal
      hcof hfib X Y V f g)

def point (side : Bool) {m : ℕ} (d : AnchoredChain g m) (t : Context X V) :
    smallParameter.{v} m 2 ⟶ (values hcof X Y V f g).obj t :=
  NerveSmallFamilies.point ((Functor.const (Context X V)).obj (smallParameter.{v} m 2))
    (values hcof X Y V f g) (NerveLargeSampling.system (values hcof X Y V f g)
      (triangle hcof hfib X Y V f g side) (test g d 2)) t

lemma point_recover (side : Bool) {m : ℕ} (d : AnchoredChain g m) (t : Context X V) :
    point hcof hfib X Y V f g side d t =
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower (test g d 2 ≫ oldTriangle hcof hfib X Y V f g side t) :=
  (NerveLargeSampling.point _ _ _ t).trans (congrArg (fun z => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower
    (test g d 2 ≫ z)) (triangle_evaluate hcof hfib X Y V f g side t))

/-- The same old all-factorization triangle is recovered in its original choice coordinates. -/
lemma original_recover (side : Bool) {m : ℕ} (d : AnchoredChain g m) (t : Context X V) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} (point hcof hfib X Y V f g side d t) ≫
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u}
        (AllFactorizationMixedContext.valueIso hcof t.1.unop.hom f g t.2.hom).hom =
    test g d 2 ≫ AllFactorizationMixed.triangle hcof hfib t.1.unop.hom.map f g t.2.hom
      (FramedResolution.frameMap t.1.unop.hom) side := by
  rw [point_recover, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map_lower, Category.assoc]
  exact congrArg (fun z => test g d 2 ≫ z)
    (AllFactorizationMixedContext.triangle_recover hcof hfib t.1.unop.hom f g t.2.hom side)

end SerrePositivity.HomotopyFunctionComplex.AllFactorizationSmallFamilies
