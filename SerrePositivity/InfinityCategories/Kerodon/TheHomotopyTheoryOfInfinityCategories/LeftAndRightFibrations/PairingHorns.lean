module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.UnionProd

/-!
概要：正則 pairing が左右のホーンだけを使う場合の anodyne 性。
方針：pairing の相対セル分解に左右のホーンの生成族を適用する。
規約：モデル構造は用いず rlp と llp の閉包だけを使う。
使われ方：Kerodon Proposition 4.2.5.3（Tag 0153）、Lemma 4.4.2.15（Tag 01A7） の prism。

対応節は Kerodon 4.2（Tag 014H）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory HomotopicalAlgebra SSet MorphismProperty MonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-- 概要：最後の面を使わない正則 pairing の包含は left anodyne。
方針：相対セル分解の全ホーンが左ホーンであることを確認する。
規約：添字の条件は pairing の型 II の単体ごとに要求する。
使われ方：Kerodon Proposition 4.2.5.3（Tag 0153） の積の左ホーン分解。 -/
lemma pairing_leftAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular]
    (hn : ∀ s : P.II, (P.isUniquelyCodimOneFace s).index rfl ≠ Fin.last (s.val.dim + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions A.ι :=
  transfiniteCompositionsOfShape_le _ _ _
    ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj ↦ by
      refine (?_ : (_ : MorphismProperty _) ≤ _) _
        (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, coproducts_le_iff]
      rintro _ _ _ ⟨c⟩
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_horn c.index (Fin.lt_last_iff_ne_last.mpr (hn c.s))⟩

/-- 概要：零番目の面を使わない正則 pairing の包含は right anodyne。
方針：相対セル分解の全ホーンが右ホーンであることを確認する。
規約：最後のホーンは許す。
使われ方：Kerodon Proposition 4.2.5.3（Tag 0153） の積の右ホーン分解。 -/
lemma pairing_rightAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular]
    (h0 : ∀ s : P.II, (P.isUniquelyCodimOneFace s).index rfl ≠ 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions A.ι :=
  transfiniteCompositionsOfShape_le _ _ _
    ⟨P.rankFunction.relativeCellComplex.toTransfiniteCompositionOfShape, fun j hj ↦ by
      refine (?_ : (_ : MorphismProperty _) ≤ _) _
        (P.rankFunction.relativeCellComplex.attachCells j hj).pushouts_coproducts
      simp only [pushouts_le_iff, coproducts_le_iff]
      rintro _ _ _ ⟨c⟩
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions_horn c.index (Fin.pos_iff_ne_zero.mpr (h0 c.s))⟩

/-- 概要：pairing core の最後以外の添字の条件から left anodyne 性を得る。
方針：core と型 II の単体の全単射で添字の条件を移す。
規約：正則性は core が与える pairing に仮定する。
使われ方：Kerodon Proposition 4.2.5.3（Tag 0153）、prism の連結した歩道。 -/
lemma pairingCore_leftAnodyneExtensions {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.PairingCore) [P.pairing.IsRegular]
    (hn : ∀ s : P.ι, P.index s ≠ Fin.last (P.dim s + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions A.ι := by
  have := (P.isProper_pairing_iff).1 (inferInstance : P.pairing.IsProper)
  apply pairing_leftAnodyneExtensions P.pairing
  intro x
  obtain ⟨s, rfl⟩ := P.equivII.surjective x
  simpa using hn s

/-- 概要：左ホーンと境界の積の和は left anodyne。
方針：Mathlib の正則 pairing core の添字が常に castSucc であることを使う。
規約：左のホーンの欠ける面は最後以外。
使われ方：Kerodon Proposition 4.2.5.3（Tag 0153）、Lemma 4.4.2.15（Tag 01A7）。 -/
lemma leftAnodyneExtensions_unionProd {m : ℕ} (k : Fin (m + 1)) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (Subcomplex.unionProd.{u} (horn (m + 1) k.castSucc) (boundary n)).ι := by
  apply pairingCore_leftAnodyneExtensions (prodStdSimplex.pairingCore k n)
  intro s
  exact Fin.castSucc_ne_last _

/-- 概要：一意な余次元一の面の番号は opposite で反転する。
方針：反転した面が目的の面となることを一意性で確認する。
規約：単体は次数を添えた SSet.S の元。
使われ方：Kerodon Proposition 4.2.5.3（Tag 0153） の左右の双対性。 -/
lemma uniquelyCodimOneFace_op_index {X : SSet.{u}} {x y : X.S}
    (h : x.IsUniquelyCodimOneFace y) : h.op.index rfl = (h.index rfl).rev := by
  obtain ⟨d, x, rfl⟩ := x.mk_surjective
  obtain ⟨d', y, rfl⟩ := y.mk_surjective
  obtain rfl : d' = d + 1 := h.dim_eq
  symm
  apply (h.op.δ_eq_iff rfl _).mp
  simpa [S.opEquiv_symm_apply] using
    congrArg (SSet.opObjEquiv (X := X) (n := Opposite.op ⦋d⦌)).symm (h.δ_index rfl)

/-- 概要：左ホーンの添字だけを使う pairing の opposite は右ホーンだけを使う。
方針：余次元一の面の添字を反転し、最後以外という条件を零以外へ移す。
規約：正則性はこの添字の補題には不要。
使われ方：Kerodon Proposition 4.2.5.3（Tag 0153） の積の右ホーン分解。 -/
lemma pairing_op_index_ne_zero {X : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsProper]
    (hn : ∀ s : P.II, (P.isUniquelyCodimOneFace s).index rfl ≠ Fin.last (s.val.dim + 1))
    (s : P.op.II) : (P.op.isUniquelyCodimOneFace s).index rfl ≠ 0 := by
  let t : P.II := ⟨Subcomplex.N.opEquiv s.val, s.property⟩
  change (P.isUniquelyCodimOneFace t).op.index rfl ≠ 0
  rw [uniquelyCodimOneFace_op_index (P.isUniquelyCodimOneFace t)]
  change ((P.isUniquelyCodimOneFace t).index rfl).rev ≠ (0 : Fin (t.val.dim + 2))
  intro h
  apply hn t
  have h' := congrArg Fin.rev h
  simpa only [Fin.rev_rev, Fin.rev_zero] using h'

/-- 概要：pairing の同型による移送は零以外の添字を保つ。
方針：対応する型 II の単体に戻し、面の番号の公式を使う。
規約：移送する同型と部分複体の逆像の等式を明示する。
使われ方：Kerodon Proposition 4.2.5.3（Tag 0153） の opposite 模型の標準化。 -/
lemma pairing_ofIso_index_ne_zero {X Y : SSet.{u}} {A : X.Subcomplex} {B : Y.Subcomplex}
    (P : A.Pairing) [P.IsProper] (e : Y ≅ X) (hA : A.preimage e.hom = B)
    (h0 : ∀ s : P.II, (P.isUniquelyCodimOneFace s).index rfl ≠ 0)
    (s : (P.ofIso e hA).II) : ((P.ofIso e hA).isUniquelyCodimOneFace s).index rfl ≠ 0 := by
  rcases s with ⟨a, ha⟩
  obtain ⟨a, rfl⟩ := (Subcomplex.N.orderIsoOfIso e hA).symm.surjective a
  simp only [Subcomplex.Pairing.ofIso_II, Set.mem_preimage, OrderIso.apply_symm_apply] at ha
  simpa only [P.ofIso_index e hA ⟨a, ha⟩ rfl] using h0 ⟨a, ha⟩

/-- 概要：最後の一次ホーンと境界の積の和は right anodyne。
方針：左側の pairing の opposite を標準単体の積へ移送する。
規約：一次ホーン Λ[1,1] は最後の頂点。
使われ方：Kerodon Proposition 4.2.5.3（Tag 0153）、Lemma 4.4.2.15（Tag 01A7） の右 prism。 -/
lemma rightAnodyneExtensions_unionProd_point (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (Subcomplex.unionProd.{u} (horn 1 1) (boundary n)).ι := by
  let e := ((stdSimplex.opIso ⦋1⦌).symm ⊗ᵢ (stdSimplex.opIso ⦋n⦌).symm) ≪≫
    Functor.Monoidal.μIso opFunctor Δ[1] Δ[n]
  have hA : (Subcomplex.unionProd.{u} (horn 1 0) (boundary n)).op.preimage e.hom =
      Subcomplex.unionProd (horn 1 1) (boundary n) := by
    dsimp [e]
    rw [Subcomplex.preimage_comp, Subcomplex.preimage_op_unionProd,
      Subcomplex.preimage_unionProd, op_boundary, op_horn, Fin.rev_zero]
    rfl
  apply pairing_rightAnodyneExtensions
    ((prodStdSimplex.pairingCore.{u} (0 : Fin 1) n).pairing.op.ofIso e hA)
  apply pairing_ofIso_index_ne_zero
  apply pairing_op_index_ne_zero
  intro s
  let P := prodStdSimplex.pairingCore.{u} (0 : Fin 1) n
  have := (P.isProper_pairing_iff).1 (inferInstance : P.pairing.IsProper)
  change (P.pairing.isUniquelyCodimOneFace s).index rfl ≠ Fin.last (s.val.dim + 1)
  obtain ⟨t, rfl⟩ := P.equivII.surjective s
  have h : P.index t ≠ Fin.last (P.dim t + 1) := Fin.castSucc_ne_last t.index
  simpa using h

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
