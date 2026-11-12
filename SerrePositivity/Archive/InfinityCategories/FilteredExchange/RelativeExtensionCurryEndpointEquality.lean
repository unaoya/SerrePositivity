module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorExtensionCurryComparison

/-!
概要：元の指定 curry 比較を、同じ実終点の等式による表示変更に沿って保持する。
方針：変更する実射だけの等式を消去し、射影と評価の証明の一意性を使う。
規約：指定比較を選び直さない。使われ方：始域恒等射付き普遍証拠の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ実始点の表示を変えても、元の指定終点比較の curry の値は保持される。 -/
lemma relativeExtensionEndpoint_curryIso_heq_of_sourceEq
    {A D C E F B L : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
    (b : A ⟶ B) (i : D ⟶ A) (hi : leftAnodyneExtensions i)
    (v : D ⟶ E) (hv : v ≫ p = i ≫ b)
    (j : C ⊗ L ⟶ A) (q : F ⟶ B) (a : C ⟶ F)
    (hj : j ≫ b = (fst C L ≫ a) ≫ q)
    (W W' : A ⟶ E) (hW : W ≫ p = b) (hW' : W' ≫ p = b)
    (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
    (g₀ g₁ g' : C ⊗ L ⟶ pullback p q)
    (hg₀ : g₀ ≫ pullback.snd p q = fst C L ≫ a)
    (hg₁ : g₁ ≫ pullback.snd p q = fst C L ≫ a)
    (hg' : g' ≫ pullback.snd p q = fst C L ≫ a)
    (hWj₀ : j ≫ W = g₀ ≫ pullback.fst p q)
    (hWj₁ : j ≫ W = g₁ ≫ pullback.fst p q)
    (hWj' : j ≫ W' = g' ≫ pullback.fst p q) (he : g₀ = g₁) :
    HEq (relativeFunctorExtensionEndpoint_curryIso p b i hi v hv j q a hj
      W W' hW hW' hWi hWi' g₀ g' hg₀ hg' hWj₀ hWj')
      (relativeFunctorExtensionEndpoint_curryIso p b i hi v hv j q a hj
        W W' hW hW' hWi hWi' g₁ g' hg₁ hg' hWj₁ hWj') := by
  cases he
  rfl

end SerrePositivity.InfinityCategories.F2
