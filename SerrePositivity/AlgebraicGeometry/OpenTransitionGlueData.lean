module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
概要：有限段に降ろす重なりの射と三重交叉の式から、実際の gluing datum を作る。
方針：三重交叉の遷移を pullback lift とし、cocycle を射影と mono 性で確認する。
規約：重なりの存在を仮定に隠した一般の模型の存在定理ではなく、貼り合わせの法則。
使われ方：G2 の有限個の射・等式から模型の Scheme.GlueData を組み立てる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {I : Type u} (U : I → Scheme.{u}) (V : I × I → Scheme.{u})
  (f : ∀ i j, V (i, j) ⟶ U i) [∀ i j, IsOpenImmersion (f i j)]
  (t : ∀ i j, V (i, j) ⟶ V (j, i))
  (L : ∀ i j k, pullback (f i j) (f i k) ⟶ V (j, k))
  (hL : ∀ i j k, L i j k ≫ f j k = pullback.fst (f i j) (f i k) ≫ t i j ≫ f j i)

include hL

/-- 三重交叉の遷移を、実際の二つの射から pullback lift で作る。 -/
def openTransitionTripleMap (i j k : I) :
    pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i) :=
  pullback.lift (L i j k) (pullback.fst (f i j) (f i k) ≫ t i j) (by simpa using hL i j k)

/-- 三重交叉の遷移の第一射影。 -/
@[reassoc (attr := simp)] theorem openTransitionTripleMap_fst (i j k : I) :
    openTransitionTripleMap U V f t L hL i j k ≫ pullback.fst (f j k) (f j i) = L i j k := by
  simp [openTransitionTripleMap]

/-- 三重交叉の遷移の第二射影。 -/
@[reassoc (attr := simp)] theorem openTransitionTripleMap_snd (i j k : I) :
    openTransitionTripleMap U V f t L hL i j k ≫ pullback.snd (f j k) (f j i) =
      pullback.fst (f i j) (f i k) ≫ t i j := by
  simp [openTransitionTripleMap]

/-- 有限個の遷移の逆と三重交叉上の式から、実際の cocycle が得られる。 -/
theorem openTransitionTripleMap_cycle
    (hinv : ∀ i j, t i j ≫ t j i = 𝟙 _)
    (hc : ∀ i j k, L i j k ≫ t j k ≫ f k j =
      pullback.snd (f i j) (f i k) ≫ t i k ≫ f k i) (i j k : I) :
    openTransitionTripleMap U V f t L hL i j k ≫
      openTransitionTripleMap U V f t L hL j k i ≫
      openTransitionTripleMap U V f t L hL k i j = 𝟙 _ := by
  let A := openTransitionTripleMap U V f t L hL i j k
  let B := openTransitionTripleMap U V f t L hL j k i
  let C := openTransitionTripleMap U V f t L hL k i j
  have hfst : A ≫ B ≫ pullback.fst (f k i) (f k j) =
      pullback.snd (f i j) (f i k) ≫ t i k := by
    apply (cancel_mono (f k i)).mp
    calc
      _ = A ≫ B ≫ pullback.snd (f k i) (f k j) ≫ f k j := by
        simp only [Category.assoc, pullback.condition]
      _ = L i j k ≫ t j k ≫ f k j := by simp [A, B]
      _ = _ := hc i j k
  have hsnd : (A ≫ B ≫ C) ≫ pullback.snd (f i j) (f i k) =
      pullback.snd (f i j) (f i k) := by
    calc
      _ = (A ≫ B ≫ pullback.fst (f k i) (f k j)) ≫ t k i := by simp [C]
      _ = (pullback.snd (f i j) (f i k) ≫ t i k) ≫ t k i := by rw [hfst]
      _ = _ := by rw [Category.assoc, hinv, Category.comp_id]
  change A ≫ B ≫ C = 𝟙 _
  apply pullback.hom_ext
  · simp only [Category.id_comp]
    apply (cancel_mono (f i j)).mp
    calc
      _ = (A ≫ B ≫ C) ≫ pullback.snd (f i j) (f i k) ≫ f i k := by
        simp only [Category.assoc, pullback.condition]
      _ = pullback.snd (f i j) (f i k) ≫ f i k := by rw [← Category.assoc, hsnd]
      _ = _ := pullback.condition.symm
  · simpa only [Category.id_comp] using hsnd

/-- 重なりの有限個の射・逆・三重交叉上の式から、実際の Scheme.GlueData を作る。 -/
def openTransitionGlueData [∀ i, IsIso (f i i)]
    (htid : ∀ i, t i i = 𝟙 _) (hinv : ∀ i j, t i j ≫ t j i = 𝟙 _)
    (hc : ∀ i j k, L i j k ≫ t j k ≫ f k j =
      pullback.snd (f i j) (f i k) ≫ t i k ≫ f k i) : Scheme.GlueData.{u} where
  J := I
  U := U
  V := V
  f := f
  f_open i j := inferInstance
  f_id i := inferInstance
  t := t
  t_id := htid
  t' := openTransitionTripleMap U V f t L hL
  t_fac i j k := openTransitionTripleMap_snd U V f t L hL i j k
  cocycle := openTransitionTripleMap_cycle U V f t L hL hinv hc

end SerrePositivity.AlgebraicGeometry
