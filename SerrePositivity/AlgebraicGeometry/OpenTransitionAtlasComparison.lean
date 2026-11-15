module

public import SerrePositivity.AlgebraicGeometry.BaseChangedGluingToBase
public import SerrePositivity.AlgebraicGeometry.CartesianBaseChangeComparison
public import SerrePositivity.AlgebraicGeometry.AtlasGluingBaseChange

/-!
概要：元のアトラスと局所模型の比較を、後段の実際の貼り合わせ全体へ移す。
方針：チャート・重なりの Cartesian 比較を底変換し、既存の貼り合わせの比較へ渡す。
規約：元の対象と被覆を保ち、係数射の単射性や忠実平坦性を仮定しない。
使われ方：G2 の一般の有限表示対象と実際の模型との Cartesian 比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 元の対象の実際の開被覆と、局所模型への Cartesian 比較の入力。 -/
structure OpenTransitionAtlasComparison {S T : Scheme.{u}}
    (C : OpenTransitionCandidate S) (g : T ⟶ S) where
  X : Scheme.{u}
  f : X ⟶ T
  U : C.J → Scheme.{u}
  j : ∀ i, U i ⟶ X
  jOpen : ∀ i, IsOpenImmersion (j i)
  cover : ∀ x : X, ∃ i z, j i z = x
  chart : ∀ i, U i ⟶ C.U i
  chartCart : ∀ i, IsPullback (chart i) (j i ≫ f) (C.p i) g
  pair : ∀ i k, pullback (j i) (j k) ⟶ C.V (i, k)
  pairCart : ∀ i k, IsPullback (pair i k) (pullback.fst (j i) (j k) ≫ j i ≫ f) (C.q i k) g
  pairToChart : ∀ i k, pair i k ≫ C.f i k = pullback.fst (j i) (j k) ≫ chart i
  pairReverse : ∀ i k, pair i k ≫ C.t i k ≫ C.f k i = pullback.snd (j i) (j k) ≫ chart k

namespace OpenTransitionAtlasComparison
variable {S T B : Scheme.{u}} {C : OpenTransitionCandidate S} {g : T ⟶ S}
  (A : OpenTransitionAtlasComparison C g) (e : T ⟶ B) (δ : B ⟶ S) (he : e ≫ δ = g)

instance (i : C.J) : IsOpenImmersion (A.j i) := A.jOpen i

/-- 元のチャートから、後段の実際のチャートへの比較。 -/
def chartAt (i : C.J) : A.U i ⟶ pullback δ (C.p i) :=
  cartesianBaseChangeComparison (A.chart i) (A.j i ≫ A.f) (C.p i) g (A.chartCart i) e δ he

/-- 元の重なりから、後段の実際の重なりへの比較。 -/
def pairAt (i j : C.J) : pullback (A.j i) (A.j j) ⟶ pullback δ (C.q i j) :=
  cartesianBaseChangeComparison (A.pair i j) (pullback.fst (A.j i) (A.j j) ≫ A.j i ≫ A.f)
    (C.q i j) g (A.pairCart i j) e δ he

/-- 重なりの後段への比較は、元の開包含と後段の開包含に関して Cartesian。 -/
theorem pairAt_square (i j : C.J) :
    IsPullback (A.pairAt e δ he i j) (pullback.fst (A.j i) (A.j j))
      (C.baseChangedF δ i j) (A.chartAt e δ he i) :=
  isPullback_cartesianBaseChangeComparison_square (A.pair i j) (A.chart i)
    (pullback.fst (A.j i) (A.j j) ≫ A.j i ≫ A.f) (A.j i ≫ A.f)
    (C.q i j) (C.p i) g (A.pairCart i j) (A.chartCart i) e δ he
    (pullback.fst (A.j i) (A.j j)) (C.f i j) (C.fOver i j) (A.pairToChart i j) rfl

/-- 元の重なりと後段の反転は、後段の実際のチャートへの射として可換。 -/
theorem pairAt_compat (i j : C.J) :
    A.pairAt e δ he i j ≫ C.baseChangedT δ i j ≫ C.baseChangedF δ j i =
      pullback.snd (A.j i) (A.j j) ≫ A.chartAt e δ he j := by
  have hr : (C.t i j ≫ C.f j i) ≫ C.p j = C.q i j := by
    rw [Category.assoc, C.fOver, C.tOver]
  have hf : A.pair i j ≫ (C.t i j ≫ C.f j i) = pullback.snd (A.j i) (A.j j) ≫ A.chart j := by
    simpa only [Category.assoc] using A.pairReverse i j
  have hx : pullback.fst (A.j i) (A.j j) ≫ A.j i ≫ A.f =
      pullback.snd (A.j i) (A.j j) ≫ A.j j ≫ A.f := by
    simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ A.f)
      (pullback.condition (f := A.j i) (g := A.j j))
  have hn := cartesianBaseChangeComparison_naturality (A.pair i j) (A.chart j)
    (pullback.fst (A.j i) (A.j j) ≫ A.j i ≫ A.f) (A.j j ≫ A.f)
    (C.q i j) (C.p j) g (A.pairCart i j) (A.chartCart j) e δ he
    (pullback.snd (A.j i) (A.j j)) (C.t i j ≫ C.f j i) hr hf hx
  simpa only [pairAt, chartAt, OpenTransitionCandidate.baseChangedT,
    OpenTransitionCandidate.baseChangedF, Category.assoc, baseChangedModelArrow_comp] using hn

/-- 元の対象から後段の実際の貼り合わせへの比較射。 -/
def gluedComparison (h : C.BaseChangedEquations δ) :
    A.X ⟶ (C.baseChangedOpenTransitionGlueData δ h).glued :=
  gluingAtlasMap (C.baseChangedOpenTransitionGlueData δ h) A.U A.j A.cover
    (A.chartAt e δ he) (A.pairAt e δ he) (A.pairAt_square e δ he) (A.pairAt_compat e δ he)

/-- 各チャートの Cartesian 比較は、元の対象と模型全体の Cartesian 比較を与える。 -/
theorem isPullback_gluedComparison (h : C.BaseChangedEquations δ) :
    IsPullback (A.gluedComparison e δ he h) A.f (C.baseChangedToBase δ h) e := by
  apply isPullback_gluingAtlasMap_toBase (C.baseChangedOpenTransitionGlueData δ h)
    A.U A.j A.cover (A.chartAt e δ he) (A.pairAt e δ he)
    (A.pairAt_square e δ he) (A.pairAt_compat e δ he)
    (fun i ↦ pullback.fst δ (C.p i)) (C.baseChangedToBase_compat δ) A.f e
  intro i
  exact isPullback_cartesianBaseChangeComparison (A.chart i) (A.j i ≫ A.f) (C.p i) g
    (A.chartCart i) e δ he

end OpenTransitionAtlasComparison
end SerrePositivity.AlgebraicGeometry
