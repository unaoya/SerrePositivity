module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorVerdierSequence
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientThickKernelEdges

/-!
概要：Milnor 条件から元対角と cell 平坦商の実 Verdier 列を接続する。
方針：D2 の完成した列と D-16 の thick 核判定を同じ四角形に特殊化する。
規約：未分解 path 商との比較や固定 ν への輸送は主張しない。
使われ方：K-10 d の resolved 射影を使う主経路の native 供給。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)

local instance : IsDGPretriangulated R (DGOdotGluing R d) :=
  dgGluingMilnor_isDGPretriangulated R d
local instance : IsExactFunctor (dgNerve.map (dgOdotQuotientInput R d).diagonal) :=
  dgGluingMilnorNativeDiagonal_isExactFunctor R d

/-- 概要：Milnor 仮定は元の指定代数比較の準同型性。
方針：D2 の条件をそのまま読む。規約：個別四角形の充満忠実性を仮定しない。
使われ方：K-10 の主張に置く環論的仮定の明示。 -/
lemma dgOdotMilnorSquare_iff : DGGluingMilnorSquare R d ↔
    QuasiIso (dgGluingMilnorSquareComparison R d).hom := Iff.rfl

/-- 概要：固定 ν の元対角は Milnor 条件から充満忠実。
方針：同じ一回 Perf 延長を比較した D2 の供給を使う。
規約：DGOdotVerdierInput の任意証人を要求しない。使われ方：固定 ν の包含欄。 -/
lemma dgOdotMilnorDiagonal_fullyFaithful (h : DGGluingMilnorSquare R d) :
    IsFullyFaithful (dgOdotDiagonalExactMap R d).hom :=
  dgGluingMilnorDiagonalExactMap_isFullyFaithful_of_milnor R d h

/-- 概要：元小 Perf 対角と同じ cell 平坦商を持つ実列。
方針：D2 の Milnor 列をそのまま束ねる。規約：旧未分解商へ戻さない。
使われ方：具体的 thick 核と局所化を備えた d③ の入力。 -/
def dgOdotMilnorNativeSequence (h : DGGluingMilnorSquare R d) : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.VerdierSequence.{u + 1} where
  left := dgGluingMilnorNativeDiagonalSource R d
  middle := dgGluingMilnorNativeMiddle R d
  right := dgGluingMilnorNativeResolvedQuotient R d
  inclusion := dgGluingMilnorNativeDiagonal R d
  projection := dgGluingMilnorResolvedProjection R d
  isVerdier := dgGluingMilnor_isResolvedVerdierSequence_of_milnor R d h

/-- 概要：resolved 射影の零対象核は元対角の本質像そのもの。
方針：D-16 の retract を含む thick 核を使った D2 の列条件を回収する。
規約：単なる安定閉包で代用しない。使われ方：d③ の実核の証拠。 -/
lemma dgOdotMilnorNativeKernel (h : DGGluingMilnorSquare R d)
    (b : (dgGluingMilnorNativeMiddle R d).obj _⦋0⦌) :
    IsZeroVertex ((dgGluingMilnorResolvedProjection R d).hom.app (Opposite.op ⦋0⦌) b) ↔
      b ∈ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.essentialImage (dgGluingMilnorNativeDiagonal R d) :=
  (dgOdotMilnorNativeSequence R d h).isVerdier.kernel b

/-- 概要：同じ実商射影は元対角像の cofiber 辺に関する局所化。
方針：D2 の実 ∞ 関手圏での普遍性を回収する。
規約：H⁰ の商だけで済ませない。使われ方：Sp の quotient 欄。 -/
lemma dgOdotMilnorNativeLocalization (h : DGGluingMilnorSquare R d) :
    IsLocalization (dgGluingMilnorResolvedProjection R d).hom
      (cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.essentialImage (dgGluingMilnorNativeDiagonal R d))) :=
  (dgOdotMilnorNativeSequence R d h).isVerdier.quotient

/-- 概要：元対角像に cofiber を持つ辺は同じ射影が反転する辺と一致する。
方針：D2 の実核を Sp 正本の完全関手の辺判定へ渡す。
規約：局所化・分数の一般補題を複製しない。使われ方：thick 核と反転辺の照合。 -/
lemma dgOdotMilnorNativeEdges (h : DGGluingMilnorSquare R d) :
    cofiberLocalizingEdges (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.essentialImage (dgGluingMilnorNativeDiagonal R d)) =
      invertedEdges (dgGluingMilnorResolvedProjection R d).hom := by
  let := (dgGluingMilnorResolvedProjection R d).isExact
  exact cofiberLocalizingEdges_eq_invertedEdges_of_kernel
    (dgGluingMilnorResolvedProjection R d).hom _ (dgOdotMilnorNativeKernel R d h)

/-- 概要：resolved 射影は同じ実 cell 分解上で元の商包含に戻る。
方針：D-9 の屋根比較を保持する。規約：分解の逆を厳密 dg 関手と扱わない。
使われ方：固定 S の二辺の屋根と native 射影の比較。 -/
def dgOdotMilnorNativeProjection_roof : FunctorIso
    (dgNerve.map (DGCategoryCellResolution.augmentation R (DGOdotGluing R d)) ≫
      (dgGluingMilnorResolvedProjection R d).hom)
    (resolvedDGQuotientProjection R (DGOdotGluing R d)
      (dgQuotientImage R (dgOdotQuotientInput R d).diagonal)) :=
  resolvedDGQuotientRoofIso R (DGOdotGluing R d) _

end SerrePositivity.KST.SConstruction
