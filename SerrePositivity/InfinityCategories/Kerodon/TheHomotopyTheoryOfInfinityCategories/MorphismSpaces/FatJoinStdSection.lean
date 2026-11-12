module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinCylinderSimplex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinStdHomotopy

/-!
概要：標準単体の fat join 比較の切断。
方針：連結した順序集合の頂点を左右へ切り詰め、切断を区間座標にする。
規約：切断は join から fat join への射。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の標準単体の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace FatJoinStd

/-- 概要：連結した頂点の順序集合を左の頂点集合へ切り詰める。
方針：左の最後の頂点との最小値を取る。
規約：右側の頂点は全て左の最後の頂点へ送る。
使われ方：Kerodon §4.6.2（Tag 01HM） の切断の左成分。 -/
def sectionLeft (n m : ℕ) : Fin (n + m + 2) →o Fin (n + 1) where
  toFun z := ⟨min z.val n, by have := min_le_right z.val n; omega⟩
  monotone' p q h := by
    change min p.val n ≤ min q.val n
    exact min_le_min h le_rfl

/-- 概要：連結した頂点の順序集合を区間に写す。
方針：左の区間は零、右の区間は一へ送る。
規約：n 以下が左の頂点。
使われ方：Kerodon §4.6.2（Tag 01HM） の切断の時間座標。 -/
def sectionTime (n m : ℕ) : Fin (n + m + 2) →o Fin 2 where
  toFun z := if z.val ≤ n then 0 else 1
  monotone' p q h := by
    by_cases hq : q.val ≤ n
    · have hp : p.val ≤ n := le_trans h hq
      dsimp only
      rw [if_pos hp, if_pos hq]
    · dsimp only
      rw [if_neg hq]
      split_ifs <;> decide

/-- 概要：連結した頂点の順序集合を右の頂点集合へ切り詰める。
方針：左の頂点数を引き、左の区間では零とする。
規約：自然数の切り捨て減算を用いる。
使われ方：Kerodon §4.6.2（Tag 01HM） の切断の右成分。 -/
def sectionRight (n m : ℕ) : Fin (n + m + 2) →o Fin (m + 1) where
  toFun z := ⟨z.val - (n + 1), by have := z.isLt; omega⟩
  monotone' _ _ h := Nat.sub_le_sub_right h (n + 1)

/-- 概要：円柱の頂点の連結を切断で戻すと左右の正規化になる。
方針：元の区間が零か一かで三つの成分を計算する。
規約：w の値は円柱比較で連結した頂点の値。
使われ方：Kerodon §4.6.2（Tag 01HM） の切断と正規化の合成の同一視。 -/
lemma section_encode (n m : ℕ) (a : Fin (n + 1)) (t : Fin 2) (b : Fin (m + 1))
    (w : Fin (n + m + 2))
    (hw : w.val = if t.val = 0 then a.val else n + 1 + b.val) :
    ((sectionLeft n m w, sectionTime n m w), sectionRight n m w) =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftClamp n (a, t), t), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightClamp m (b, t)) := by
  fin_cases t
  · change w.val = a.val at hw
    have ha : a.val ≤ n := Nat.le_of_lt_succ a.isLt
    have hwle : w.val ≤ n := by omega
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · apply Fin.ext
      change min w.val n = a.val
      rw [hw, min_eq_left ha]
    · change (if w.val ≤ n then (0 : Fin 2) else 1) = 0
      rw [if_pos hwle]
    · apply Fin.ext
      change w.val - (n + 1) = 0
      omega
  · change w.val = n + 1 + b.val at hw
    have hwn : n < w.val := by omega
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · apply Fin.ext
      change min w.val n = n
      exact min_eq_right (Nat.le_of_lt hwn)
    · change (if w.val ≤ n then (0 : Fin 2) else 1) = 1
      rw [if_neg (Nat.not_le_of_lt hwn)]
    · apply Fin.ext
      change w.val - (n + 1) = b.val
      omega

end FatJoinStd

/-- 概要：連結した標準単体から左右と区間の円柱への切断。
方針：三つの単調写像を直積にする。
規約：fat join への包含を合成する前の射。
使われ方：Kerodon §4.6.2（Tag 01HM） の切断と正規化の計算。 -/
noncomputable def fatJoinStdSectionCylinder (n m : ℕ) :
    (Δ[n + m + 1] : SSet.{u}) ⟶ ((Δ[n] : SSet.{u}) ⊗ Δ[1]) ⊗ Δ[m] :=
  lift (lift (stdSimplex.map (SimplexCategory.mkHom (FatJoinStd.sectionLeft n m)))
      (stdSimplex.map (SimplexCategory.mkHom (FatJoinStd.sectionTime n m))))
    (stdSimplex.map (SimplexCategory.mkHom (FatJoinStd.sectionRight n m)))

/-- 概要：連結した標準単体から fat join への切断の射。
方針：左右への切り詰めと区間座標を直積にして円柱へ写す。
規約：始域の次数は n+m+1。
使われ方：Kerodon §4.6.2（Tag 01HM） の標準単体の切断。 -/
noncomputable def fatJoinStdSectionSimplex (n m : ℕ) :
    (Δ[n + m + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[n] : SSet.{u}) Δ[m] :=
  fatJoinStdSectionCylinder n m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder Δ[n] Δ[m]

/-- 概要：標準単体の join から fat join への切断。
方針：通常の join の標準単体との同型に続けて切断を適用する。
規約：比較と逆向きの射。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の標準単体の比較。 -/
noncomputable def fatJoinStdSection (n m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[m] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[n] : SSet.{u}) Δ[m] :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n m).hom ≫ fatJoinStdSectionSimplex n m

/-- 概要：標準単体から切断して比較し直すと元の標準単体の射になる。
方針：円柱比較の頂点の式を切断の左右で計算する。
規約：全ての次数での厳密な恒等式。
使われ方：Kerodon §4.6.2（Tag 01HM） の切断の検証。 -/
lemma fatJoinStdSectionSimplex_comparison (n m : ℕ) :
    fatJoinStdSectionSimplex.{u} n m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison Δ[n] Δ[m] ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n m).hom = 𝟙 (Δ[n + m + 1] : SSet.{u}) := by
  unfold fatJoinStdSectionSimplex
  rw [Category.assoc, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder Δ[n] Δ[m])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison Δ[n] Δ[m]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n m).hom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_comparison]
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro z
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n m).hom.app (Opposite.op ⦋d⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap Δ[n] Δ[m]).app (Opposite.op ⦋d⦌)
      (((stdSimplex.map (SimplexCategory.mkHom (FatJoinStd.sectionLeft n m))).app
          (Opposite.op ⦋d⦌) z,
        (stdSimplex.map (SimplexCategory.mkHom (FatJoinStd.sectionTime n m))).app
          (Opposite.op ⦋d⦌) z),
       (stdSimplex.map (SimplexCategory.mkHom (FatJoinStd.sectionRight n m))).app
          (Opposite.op ⦋d⦌) z)) i).val = (z i).val
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinCylinderMap_stdSimplex_val]
  change (if (if (z i).val ≤ n then (0 : Fin 2) else 1).val = 0 then
    min (z i).val n else n + 1 + ((z i).val - (n + 1))) = (z i).val
  by_cases hz : (z i).val ≤ n
  · rw [if_pos hz]
    change min (z i).val n = (z i).val
    exact min_eq_left hz
  · rw [if_neg hz]
    change n + 1 + ((z i).val - (n + 1)) = (z i).val
    omega

/-- 概要：標準単体の fat join 比較には厳密な切断がある。
方針：標準単体への同型で右から比較して前の恒等式を適用する。
規約：この切断だけでは比較の同値条件は結論しない。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の切断。 -/
lemma fatJoinStdSection_comparison (n m : ℕ) :
    fatJoinStdSection.{u} n m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinComparison Δ[n] Δ[m] =
      𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[m]) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n m).hom).1
  unfold fatJoinStdSection
  simp only [Category.assoc, fatJoinStdSectionSimplex_comparison, Category.comp_id,
    Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
