module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedKanWhitehead
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses

/-!
概要：全単射に対する RLP を持つ射への同じ合成は同じ点つき成分を与える。
方針：基点を固定する垂直ホモトピーを成分の等式へ送る。
規約：左側の源に Kan 性を要求しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。厳密な列の切断から段ごとのホモトピー逆を検証する。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.PointedMapping

noncomputable section

/-- 概要：全単射 RLP 射への合成が等しい二つの点つき射は同じ成分を持つ。
方針：基点を固定する垂直ホモトピーの存在を使う。
規約：全空間 E は Kan、底 B に Kan 性を要求しない。
使われ方：Goerss–Jardine I §7。mapping path の切断の左右の逆の検証。 -/
theorem componentOf_eq_of_comp_eq_rlp {A E B : PointedSimplicialSet.{u}} [KanComplex E.right]
    (p : E ⟶ B) (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p.right)
    (a b : A ⟶ E) (h : a ≫ p = b ≫ p) : componentOf a = componentOf b :=
  (piZero_eq_iff_pointedHomotopy a b).mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exists_pointedHomotopy_of_comp_eq p hp a b h)

end

end SerrePositivity.KST.Spectra.PointedMapping
