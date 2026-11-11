module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentFaceDegree
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeOneBoundary

/-!
# coherent 単体の有限内部点の微分方程式

概要：標準成分の微分を、各内部点での合成成分と削除成分の差の降順符号付き和で表す。
方針：立方体境界を同じ次数の面の式へ移し、降順番号付けを内部点の集合に再添字付けする。
規約：符号の指数はその内部点より大きい内部点の個数である。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の比較写像の dg 単体の方程式の組立て。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory CategoryTheory.SimplicialThickening DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]
variable {J : Type u} [LinearOrder J] {a b : J}

/-- 概要：正の座標数を持つ coherent 成分の微分は内部点の合成と削除の差の交代和である。
方針：降順番号付けで立方体の微分公式を使い、面の評価を同じ次数の成分へ直す。
規約：始次数 k と終次数 l を指定し、l=k+1 を仮定する。
使われ方：HA 1.3.1.16 の非空の内部点集合の方程式。 -/
lemma coherentCubeComponentAt_d_of_enumeration
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    (hab : a < b) {S : Finset (Set.Ioo a b)} {m : ℕ}
    (e : Fin (m + 1) ≃ S) (he : StrictAnti e) (k l : ℤ)
    (hk : k = -(S.card : ℤ)) (hl : l = k + 1) :
    (homObject R D (s.obj (.mk a)) (s.obj (.mk b))).d k l
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt s hab S k hk) =
      ∑ j : S, (-1 : ℤ) ^ (S.filter (j.val < ·)).card •
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeCompositionAt s hab S j l (by omega) -
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt s hab (S.erase j.val) l
            (by have hE := Finset.card_erase_add_one j.property; omega)) := by
  have hS : S.card = m + 1 := by simpa using (Fintype.card_congr e).symm
  have hk' : k = -((m + 1 : ℕ) : ℤ) := by rw [hS] at hk; exact hk
  have hl' : l = -(m : ℤ) := by omega
  subst hk'
  subst hl'
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_coherent_eq_componentAt s hab e he hk]
  refine (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_succ_d e (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom s hab S)).trans ?_
  let term (j : S) := (-1 : ℤ) ^ (S.filter (j.val < ·)).card •
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeCompositionAt s hab S j (-(m : ℤ)) (by omega) -
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt s hab (S.erase j.val) (-(m : ℤ))
        (by have hE := Finset.card_erase_add_one j.property; omega))
  refine Eq.trans ?_ (Fintype.sum_equiv e (fun i ↦ term (e i)) term (fun _ ↦ rfl))
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [term]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.strictAnti_enumeration_card_filter e he i,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_coherent_face_one_at s hab e he i (by omega),
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_coherent_face_zero_at s hab e he i
      (by have hE := Finset.card_erase_add_one (e i).property; omega)]

/-- 概要：任意の有限内部点集合の標準成分は合成面と削除面による微分方程式を満たす。
方針：座標数が正なら降順の全単射を選び、零なら零次立方体評価の閉性を使う。
規約：微分は k から l=k+1。空の和は零であり、辺の閉性も含む。
使われ方：HA 1.3.1.16 の比較写像の全ての成分の dg 方程式の内部点表示。 -/
lemma coherentCubeComponentAt_d
    (s : EnrichedFunctor SSet (SimplicialThickening J) (ClosedCategory R D))
    (hab : a < b) (S : Finset (Set.Ioo a b)) (k l : ℤ)
    (hk : k = -(S.card : ℤ)) (hl : l = k + 1) :
    (homObject R D (s.obj (.mk a)) (s.obj (.mk b))).d k l
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt s hab S k hk) =
      ∑ j : S, (-1 : ℤ) ^ (S.filter (j.val < ·)).card •
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeCompositionAt s hab S j l (by omega) -
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt s hab (S.erase j.val) l
            (by have hE := Finset.card_erase_add_one j.property; omega)) := by
  cases hS : S.card with
  | zero =>
    have hk' : k = 0 := by omega
    have hl' : l = 1 := by omega
    subst hk'
    subst hl'
    let e : Fin 0 ≃ S := Fin.revPerm.trans (S.orderIsoOfFin hS).toEquiv
    have he : StrictAnti e := by intro i; exact Fin.elim0 i
    have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt s hab S 0 hk = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation e (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeHom s hab S) :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_coherent_eq_componentAt s hab e he (by omega)).symm
    rw [hv]
    refine (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_zero_closed e _).trans ?_
    symm
    apply Finset.sum_eq_zero
    intro j _
    exfalso
    have h := Finset.card_pos.mpr (show S.Nonempty from ⟨j.val, j.property⟩)
    omega
  | succ m =>
    let e : Fin (m + 1) ≃ S := Fin.revPerm.trans (S.orderIsoOfFin hS).toEquiv
    exact coherentCubeComponentAt_d_of_enumeration s hab e
      ((S.orderIsoOfFin hS).strictMono.comp_strictAnti Fin.rev_strictAnti) k l hk hl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
