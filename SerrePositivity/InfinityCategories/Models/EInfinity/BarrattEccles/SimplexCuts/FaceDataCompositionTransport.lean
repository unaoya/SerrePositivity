module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.FaceDataOrderTransport

/-!
模型。文献の定義との比較は後で
# 外側の指定面を通した同じ頂点列の移送

Berger–Fresse §2.2.6、M14 L12a のC451hの挿入色への証明分割。
元の全頂点の順序同値に沿い、同じ外側の面を合成する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 同じ順序列挙と指定頂点の合成は、元の指定面を保つ（BF §2.2.6）。 -/
lemma faceData_comp_eq_of_colorOrderIso {m m' q q' r r' : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m' q')
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r' (m' + 1)) (a : Fin r) (b : Fin r')
    (ρ : Fin (q' + 1) →o Fin (q + 1))
    (e : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u.val a) ≃o ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions t v.val b))
    (hv : ∀ x, s.vertical x.val = ρ (t.vertical (e x).val)) :
    (⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s u a, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices s u a⟩ : Σ d : ℕ, Fin (d + 1) →o Fin (q + 1)) =
      ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree t v b, ρ.comp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices t v b)⟩ := by
  have hc : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u.val a).card = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions t v.val b).card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr e.toEquiv
  have hd : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s u a = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree t v b := congrArg (fun n : ℕ => n - 1) hc
  apply Sigma.ext hd
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.orderHom_heq_of_values _ _ (congrArg (fun n : ℕ => n + 1) hd)
  intro i j hij
  let first := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s u.val a).orderIsoOfFin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions_card_eq s u a)
  let last := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions t v.val b).orderIsoOfFin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions_card_eq t v b)
  let f := first.trans (e.trans last.symm)
  have he : f i = j := Fin.ext ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.finiteOrderIso_val f i).trans hij)
  have hep : e (first i) = last j := by
    have h := congrArg last he
    change last (last.symm (e (first i))) = last j at h
    simpa only [OrderIso.apply_symm_apply] using h
  have hvertex := hv (first i)
  rw [hep] at hvertex
  exact hvertex


end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
