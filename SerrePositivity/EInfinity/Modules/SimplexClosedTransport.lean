module
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.DifferentialGraded.Functor.DGClosedIsoConjugation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FunctorMapping

/-!
概要：元の dg 単体の対象表示を閉零同型で移し、全 cochain と HA 方程式を保つ。
方針：頂点ラベルに全 Hom を引き戻し、既存の dg 共役関手で単体を送る。
規約：HA Construction 1.3.1.6、全有限部分集合・全次数。
使われ方：M10 の元の全三相単体の評価と符号付き frame 表示の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.KST.SConstruction
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 概要：同じ単体を頂点ラベル間の全 Hom に表示する。
方針：元の全 cochain と全 HA 方程式をそのまま使う。
規約：HA 1.3.1.6、頂点が重なる場合も可。使われ方：対象表示の移送。 -/
def simplexVertexLabels {n : ℕ} (s : Simplex A D n) :
    letI := inducedDGCategory A s.obj
    Simplex A (Fin (n + 1)) n := by
  letI := inducedDGCategory A s.obj
  exact { obj := id
          hom := s.hom
          equation := s.equation }

/-- 概要：元の全単体を同じ閉零同型による対象表示へ移す。
方針：既存の全 dg 共役関手でラベル付きの元の単体を送る。
規約：HA 1.3.1.6、全 cochain。使われ方：評価した三相対象の比較。 -/
def simplexClosedTransport {n : ℕ} (s : Simplex A D n) (b : Fin (n + 1) → D)
    (e : ∀ i, ForgetEnrichment.of (Complex A) (s.obj i) ≅
      ForgetEnrichment.of (Complex A) (b i)) : Simplex A D n := by
  letI := inducedDGCategory A s.obj
  exact (simplexVertexLabels A D s).map
    (dgFunctorClosedConjugate A (inducedDGEvaluation A s.obj) b e)

/-- 概要：表示移送後の対象は元の指定対象族。
方針：既存の共役関手の対象写像を評価する。
規約：HA 1.3.1.6。使われ方：実三相頂点の同定。 -/
lemma simplexClosedTransport_obj {n : ℕ} (s : Simplex A D n)
    (b : Fin (n + 1) → D)
    (e : ∀ i, ForgetEnrichment.of (Complex A) (s.obj i) ≅
      ForgetEnrichment.of (Complex A) (b i)) (i : Fin (n + 1)) :
    (simplexClosedTransport A D s b e).obj i = b i := rfl

/-- 概要：全 cochain の表示移送は元の二つの閉零同型による前後合成。
方針：既存の dg 共役関手の全 Hom 複体の作用を評価する。
規約：HA 1.3.1.6、任意整数次数。使われ方：全三相係数の比較。 -/
lemma simplexClosedTransport_hom {n : ℕ} (s : Simplex A D n)
    (b : Fin (n + 1) → D)
    (e : ∀ i, ForgetEnrichment.of (Complex A) (s.obj i) ≅
      ForgetEnrichment.of (Complex A) (b i))
    (I : Finset (Fin (n + 1))) (a c : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hc : c = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (simplexClosedTransport A D s b e).hom I a c k hI ha hc hk =
      (enrichedClosedIsoConjugation (Complex A) (e a) (e c)).f k
        (s.hom I a c k hI ha hc hk) := by
  change (𝟙 _ ≫ enrichedClosedIsoConjugation (Complex A) (e a) (e c)).f k
    (s.hom I a c k hI ha hc hk) = _
  rw [Category.id_comp]

end SerrePositivity.EInfinity.Modules
