module

public import SerrePositivity.AlgebraicGeometry.BaseChangedModelTripleProjections

/-!
概要：gluing の単位・逆・三重交叉の式を同じ段へ降ろすための具体的な局所射の入力。
方針：チャート・重なりと構造射の可換式を保ったまま実際に底変換する。
規約：六種の gluing の式は別に供給する。一般の模型の存在を仮定する出口ではない。
使われ方：G2 の具体的な六種の式から実際の貼り合わせへ渡す入力。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 構造射の可換式を保つチャート・重なり・対角・反転・三重交叉の具体的な入力。 -/
structure OpenTransitionCandidate (S : Scheme.{u}) where
  J : Type u
  U : J → Scheme.{u}
  V : J × J → Scheme.{u}
  p : ∀ i, U i ⟶ S
  q : ∀ i j, V (i, j) ⟶ S
  f : ∀ i j, V (i, j) ⟶ U i
  fOpen : ∀ i j, IsOpenImmersion (f i j)
  fOver : ∀ i j, f i j ≫ p i = q i j
  d : ∀ i, U i ⟶ V (i, i)
  dOver : ∀ i, d i ≫ q i i = p i
  t : ∀ i j, V (i, j) ⟶ V (j, i)
  tOver : ∀ i j, t i j ≫ q j i = q i j
  L : ∀ i j k, pullback (f i j) (f i k) ⟶ V (j, k)
  LOver : ∀ i j k, L i j k ≫ q j k = pullback.fst (f i j) (f i k) ≫ f i j ≫ p i

namespace OpenTransitionCandidate
variable {S B : Scheme.{u}} (C : OpenTransitionCandidate S) (γ : B ⟶ S)

/-- 後段の実際の重なりからチャートへの射。 -/
def baseChangedF (i j : C.J) : pullback γ (C.q i j) ⟶ pullback γ (C.p i) :=
  baseChangedModelArrow γ (C.q i j) (C.p i) (C.f i j) (C.fOver i j)

/-- 後段の対角の逆の候補。 -/
def baseChangedD (i : C.J) : pullback γ (C.p i) ⟶ pullback γ (C.q i i) :=
  baseChangedModelArrow γ (C.p i) (C.q i i) (C.d i) (C.dOver i)

/-- 後段の実際の重なりの反転。 -/
def baseChangedT (i j : C.J) : pullback γ (C.q i j) ⟶ pullback γ (C.q j i) :=
  baseChangedModelArrow γ (C.q i j) (C.q j i) (C.t i j) (C.tOver i j)

/-- 後段の実際の交叉へ移送した三重交叉の射。 -/
def baseChangedL (i j k : C.J) :
    pullback (C.baseChangedF γ i j) (C.baseChangedF γ i k) ⟶ pullback γ (C.q j k) :=
  (baseChangedModelTripleIso γ (C.p i) (C.q i j) (C.q i k)
    (C.f i j) (C.f i k) (C.fOver i j) (C.fOver i k)).hom ≫
    baseChangedModelArrow γ (pullback.fst (C.f i j) (C.f i k) ≫ C.f i j ≫ C.p i)
      (C.q j k) (C.L i j k) (C.LOver i j k)

instance (i j : C.J) : IsOpenImmersion (C.baseChangedF γ i j) := by
  letI : IsOpenImmersion (C.f i j) := C.fOpen i j
  exact isOpenImmersion_baseChangedModelArrow γ (C.q i j) (C.p i) (C.f i j) (C.fOver i j)

/-- 後段の開包含の基底上の可換式。 -/
@[reassoc (attr := simp)] theorem baseChangedF_toBase (i j : C.J) :
    C.baseChangedF γ i j ≫ pullback.fst γ (C.p i) = pullback.fst γ (C.q i j) := by
  simp [baseChangedF]

/-- 後段の対角の候補の基底上の可換式。 -/
@[reassoc (attr := simp)] theorem baseChangedD_toBase (i : C.J) :
    C.baseChangedD γ i ≫ pullback.fst γ (C.q i i) = pullback.fst γ (C.p i) := by
  simp [baseChangedD]

/-- 後段の反転の基底上の可換式。 -/
@[reassoc (attr := simp)] theorem baseChangedT_toBase (i j : C.J) :
    C.baseChangedT γ i j ≫ pullback.fst γ (C.q j i) = pullback.fst γ (C.q i j) := by
  simp [baseChangedT]

/-- 実際の交叉へ移送後の三重交叉の射も基底座標を保持する。 -/
@[reassoc (attr := simp)] theorem baseChangedL_toBase (i j k : C.J) :
    C.baseChangedL γ i j k ≫ pullback.fst γ (C.q j k) =
      pullback.fst (C.baseChangedF γ i j) (C.baseChangedF γ i k) ≫
        C.baseChangedF γ i j ≫ pullback.fst γ (C.p i) := by
  simp [baseChangedL, baseChangedF, Category.assoc]

end OpenTransitionCandidate
end SerrePositivity.AlgebraicGeometry
