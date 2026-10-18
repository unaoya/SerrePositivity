module

public import SerrePositivity.KST.DerivedBlowup.UniversalPresentation

/-!
概要：KST Def3.1 の普遍チャート関係式を独立モニック変数の表示へ移す。
方針：T_i と比座標を係数環へ置き、残りの T_j を外側の多項式変数にする。
規約：変数の再配置のみ。商を取らない通常の多項式環の比較。
使われ方：普遍チャート関係式の弱正則性の証明。
-/

@[expose] public noncomputable section

universe v

namespace SerrePositivity.KST.DerivedBlowup

variable {I : Type v} [DecidableEq I]

/-- 概要：T_i と比座標を係数に持ち、残りの T_j を変数にする環。
方針：UniversalChart を係数にした多項式環を使う。
規約：KST Def3.1。使われ方：関係式をモニック族として読む。 -/
abbrev UniversalSplitRing (i : I) := MvPolynomial (ChartIndex i) (UniversalChart i)

/-- 概要：普遍基底の T_j を再配置した環へ送る。
方針：pivot は係数の radial 変数、それ以外は外側の変数に送る。
規約：KST Def3.1。使われ方：再配置射の係数部分。 -/
def universalSplitCoefficientMap (i : I) : UniversalBase I →+* UniversalSplitRing i :=
  MvPolynomial.eval₂Hom (Int.castRingHom _)
    (fun j => if h : j = i then MvPolynomial.C (radialCoordinate i)
      else MvPolynomial.X ⟨j, h⟩)

/-- 概要：普遍表示環の変数を独立モニック変数の順へ再配置する。
方針：基底 T_j の再配置と比座標の係数への包含を合わせる。
規約：KST Def3.1。使われ方：普遍関係式のモニック表示。 -/
def universalSplitMap (i : I) : ChartRing (UniversalBase I) i →+* UniversalSplitRing i :=
  MvPolynomial.eval₂Hom (universalSplitCoefficientMap i)
    (fun j => MvPolynomial.C (MvPolynomial.X (some j)))

/-- 概要：radial・比座標の自由環を元の普遍表示環へ戻す。
方針：none は T_i、some j は比座標の変数へ送る。
規約：KST Def3.1。使われ方：再配置の逆射の係数部分。 -/
def universalFreeChartMap (i : I) : UniversalChart i →+* ChartRing (UniversalBase I) i :=
  MvPolynomial.eval₂Hom (Int.castRingHom _)
    (fun j => match j with
      | none => MvPolynomial.C (MvPolynomial.X i)
      | some j => MvPolynomial.X j)

/-- 概要：独立モニック変数の表示から元の普遍表示環へ戻す。
方針：係数環の自由座標を戻し、外側の T_j を元の係数へ送る。
規約：KST Def3.1。使われ方：再配置同型の逆射。 -/
def universalUnsplitMap (i : I) : UniversalSplitRing i →+* ChartRing (UniversalBase I) i :=
  MvPolynomial.eval₂Hom (universalFreeChartMap i) (fun j => MvPolynomial.C (MvPolynomial.X j.val))

/-- 概要：普遍関係式は再配置後に係数から独立変数を引く形になる。
方針：T_i・T_j・S_j の各像を代入する。
規約：KST Def3.1。使われ方：負のモニック関係族としての正則性。 -/
theorem universalSplitMap_relation (i : I) (j : ChartIndex i) :
    universalSplitMap i (universalRelation i j) =
      MvPolynomial.C (radialCoordinate i * MvPolynomial.X (some j)) - MvPolynomial.X j := by
  simp [universalSplitMap, universalSplitCoefficientMap, universalRelation,
    chartRelation, chartCoordinate, j.property, map_sub, map_mul]

/-- 概要：変数再配置の後に逆再配置すると恒等になる。
方針：比変数と基底変数をそれぞれ比較する。
規約：KST Def3.1。使われ方：再配置環同型の左逆。 -/
theorem universalUnsplitMap_comp_split (i : I) :
    (universalUnsplitMap i).comp (universalSplitMap i) =
      RingHom.id (ChartRing (UniversalBase I) i) := by
  apply MvPolynomial.ringHom_ext'
  · apply MvPolynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · intro j
      by_cases hj : j = i
      · subst j
        simp [universalUnsplitMap, universalSplitMap, universalSplitCoefficientMap,
          universalFreeChartMap, radialCoordinate]
      · simp [universalUnsplitMap, universalSplitMap, universalSplitCoefficientMap, hj]
  · intro j
    simp [universalUnsplitMap, universalSplitMap, universalFreeChartMap]

/-- 概要：逆再配置の後に変数再配置すると恒等になる。
方針：外側の T_j と内側の radial・比変数で確認する。
規約：KST Def3.1。使われ方：再配置環同型の右逆。 -/
theorem universalSplitMap_comp_unsplit (i : I) :
    (universalSplitMap i).comp (universalUnsplitMap i) =
      RingHom.id (UniversalSplitRing i) := by
  apply MvPolynomial.ringHom_ext'
  · apply MvPolynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · intro j
      cases j with
      | none => simp [universalUnsplitMap, universalSplitMap, universalSplitCoefficientMap,
          universalFreeChartMap, radialCoordinate]
      | some j => simp [universalUnsplitMap, universalSplitMap, universalFreeChartMap]
  · intro j
    simp [universalUnsplitMap, universalSplitMap, universalSplitCoefficientMap, j.property]

/-- 概要：普遍表示環と独立モニック変数表示の環同型。
方針：生成元で証明した相互逆射を束ねる。
規約：KST Def3.1。使われ方：普遍関係式の弱正則性を移送する。 -/
def universalSplitEquiv (i : I) :
    ChartRing (UniversalBase I) i ≃+* UniversalSplitRing i :=
  RingEquiv.ofRingHom (universalSplitMap i) (universalUnsplitMap i)
    (universalSplitMap_comp_unsplit i) (universalUnsplitMap_comp_split i)

end SerrePositivity.KST.DerivedBlowup
