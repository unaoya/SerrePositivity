module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.EInfinity.BarrattEccles.ConnectiveCover
public import SerrePositivity.EInfinity.Operad.ZeroTruncation

/-!
# 実 E 代数の零次集中模型と元の切断二射

概要：元の E 代数に τ≥0τ≤0 の全 E 代数構造と同じ包含・商射を与える。
方針：実 E の非正次数性を全入力の切断降下に代入する。
規約：元の底が零次ホモロジーに集中すれば、同じ二射が擬同型となる。
使われ方：離散可換代数の本質像への逆包含。通常可換代数との同定は後続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A]

def zeroTruncation (B : (operad A).Algebra) [B.carrier.IsStrictlyLE 0] : (operad A).Algebra :=
  Operad.Algebra.zeroTruncation (arity_nonpositive A) B

def zeroTruncationProjection (B : (operad A).Algebra) [B.carrier.IsStrictlyLE 0] :
    B ⟶ zeroTruncation A B :=
  Operad.Algebra.zeroTruncationProjection (arity_nonpositive A) B

lemma connectiveCover_nonpositive (B : (operad A).Algebra) :
    (connectiveCover A B).carrier.IsStrictlyLE 0 := by
  change (B.carrier.truncLE 0).IsStrictlyLE 0
  infer_instance

def zeroDegreeModel (B : (operad A).Algebra) : (operad A).Algebra := by
  let := connectiveCover_nonpositive A B
  exact zeroTruncation A (connectiveCover A B)

def zeroDegreeModelProjection (B : (operad A).Algebra) :
    connectiveCover A B ⟶ zeroDegreeModel A B := by
  let := connectiveCover_nonpositive A B
  exact zeroTruncationProjection A (connectiveCover A B)

lemma zeroDegreeModel_nonpositive (B : (operad A).Algebra) :
    (zeroDegreeModel A B).carrier.IsStrictlyLE 0 := by
  let := connectiveCover_nonpositive A B
  exact Operad.Algebra.zeroTruncation_nonpositive (arity_nonpositive A) (connectiveCover A B)

lemma zeroDegreeModel_nonnegative (B : (operad A).Algebra) :
    (zeroDegreeModel A B).carrier.IsStrictlyGE 0 := by
  let := connectiveCover_nonpositive A B
  exact Operad.Algebra.zeroTruncation_nonnegative (arity_nonpositive A) (connectiveCover A B)

lemma zeroDegreeModelProjection_quasiIso (B : (operad A).Algebra)
    [B.carrier.IsLE 0] [B.carrier.IsGE 0] : QuasiIso (zeroDegreeModelProjection A B).hom := by
  let := connectiveCover_nonpositive A B
  have := connectiveCoverInclusion_quasiIso A B
  have : (connectiveCover A B).carrier.IsGE 0 := by
    change (connectiveCover A B).carrier.IsSupported (ComplexShape.embeddingUpIntGE 0)
    exact (HomologicalComplex.isSupported_iff_of_quasiIso
      (connectiveCoverInclusion A B).hom (ComplexShape.embeddingUpIntGE 0)).mpr inferInstance
  exact Operad.Algebra.zeroTruncationProjection_quasiIso
    (arity_nonpositive A) (connectiveCover A B)

end SerrePositivity.EInfinity.BarrattEccles

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.1.3.15" (partial := component) "仮定：通常可換環上の厳密に非正次数の非可換 dg 代数、または実 Barratt–Eccles 代数（Lean が強い：厳密な dg 模型の場合）。結論：非可換 dg 代数には全 n≥0 の Postnikov 切断・代数射を構成し、次数 n 以下の群の同型と n より大きい群の消滅を示す。実 E 代数には n=0 の台の切断に同じオペラッド代数構造と射を与える（指定した模型での代数構造と基礎切断の一致の部分に一致）。任意 n の Eₖ モノイダル整合性、切断普遍性、HA の模型との比較は含まれない。"] _root_.SerrePositivity.EInfinity.BarrattEccles.zeroTruncation
attribute [cite HA "7.1.3.15" (partial := component) "仮定：通常可換環上の厳密に非正次数の非可換 dg 代数、または実 Barratt–Eccles 代数（Lean が強い：厳密な dg 模型の場合）。結論：非可換 dg 代数には全 n≥0 の Postnikov 切断・代数射を構成し、次数 n 以下の群の同型と n より大きい群の消滅を示す。実 E 代数には n=0 の台の切断に同じオペラッド代数構造と射を与える（指定した模型での代数構造と基礎切断の一致の部分に一致）。任意 n の Eₖ モノイダル整合性、切断普遍性、HA の模型との比較は含まれない。"] _root_.SerrePositivity.EInfinity.BarrattEccles.zeroTruncationProjection
