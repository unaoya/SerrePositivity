module
public import SerrePositivity.KST.Fibration.RelativeFirstRowQuotient
public import SerrePositivity.KST.Fibration.QuotientSKernelPositiveStages

/-!
概要：同じ有限第一行の商比較を、元の相対 S• の実現と Ex∞ 核四角形へ渡す。
方針：第一行の厳密比較で正段入力を移し、既証明の零段と対角実現を使う。
規約：第一行商比較の可逆性に条件付き。一般局所化性やその core 比較は主張しない。
使われ方：K-6 c5 の Sp 正本の有限図式供給を受ける具体的な利用側。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)

/-- 概要：正段の同じ第一行図式を標準単体の座標で読む。
方針：K-S• 正本の第一行と標準単体の同型に内部 Hom を適用する。
規約：図式の値を変えず、第一行の添字だけを移す。
使われ方：Sp の有限線型図式の供給型との照合。 -/
def relativeFirstRowSimplexIso (n : ℕ) (X : SSet.{u}) :
    (ihom (firstRowNerve (n + 1))).obj X ≅ (ihom (Δ[n] : SSet.{u})).obj X :=
  (internalHom.mapIso (firstRowSimplexIso n).op).app X

/-- 概要：標準単体への座標同型は同じ商関手の全後合成を厳密に保つ。
方針：同じ内部 Hom の自然同型の自然性を使う。
規約：元の商射そのものとの厳密等式。
使われ方：有限線型図式供給を別の商に置き換えずに消費する。 -/
theorem relativeFirstRowSimplexIso_postcomp (n : ℕ) :
    (ihom (firstRowNerve (n + 1))).map q.hom ≫
        (relativeFirstRowSimplexIso n C.obj).hom =
      (relativeFirstRowSimplexIso n B.obj).hom ≫ (ihom (Δ[n] : SSet.{u})).map q.hom :=
  (internalHom.mapIso (firstRowSimplexIso n).op).hom.naturality q.hom

/-- 概要：元の商比較の全正段入力は同じ有限第一行の全比較と同値。
方針：元の相対第一行四角形による各段の必要十分条件を使う。
規約：可逆性自体は証明せず、Sp への供給対象を具体的な同じ射に限定する。
使われ方：同じ実 dg 列の既存 hstage 引数への代入。 -/
theorem relativeSQuotient_positive_stages_iff_firstRows :
    (∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map (relativeSQuotientMap q (n + 1)))) ↔
      ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
        (relativeFirstRowQuotient q (n + 1))) := by
  constructor
  · intro h n
    exact (relativeSQuotient_localized_isIso_iff_firstRow q (n + 1)).mp (h n)
  · intro h n
    exact (relativeSQuotient_localized_isIso_iff_firstRow q (n + 1)).mpr (h n)

/-- 概要：同じ有限第一行の商比較に条件付きで、元の相対 S• 商実現射が可逆。
方針：第一行の正段入力と既証明の零段を同じ対角実現へ渡す。
規約：商実現比較の無条件性は主張しない。
使われ方：K-6 c5 の元の商実現射に対する有限図式供給の消費。 -/
theorem relativeSQuotientRealization_localized_isIso_of_firstRows
    (hq : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeFirstRowQuotient q (n + 1)))) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (simplicialDiagonalFunctor.map (relativeSimplicialQuotientMap q))) :=
  relativeSQuotientRealization_localized_isIso_of_positive_stages q
    ((relativeSQuotient_positive_stages_iff_firstRows q).mpr hq)

/-- 概要：同じ有限第一行の比較に条件付きで、元の商実現の Ex∞ 射が同値。
方針：第一行の全正段比較を元の Ex∞ 商実現比較へ渡す。
規約：新しい局所化存在や全四角形比較は仮定しない。
使われ方：K-6 c5 の同じ実商の全写像空間比較。 -/
theorem relativeSQuotientKanMap_isQCatEquivalence_of_firstRows
    (hq : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeFirstRowQuotient q (n + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map
      (simplicialDiagonalFunctor.map (relativeSimplicialQuotientMap q))) :=
  relativeSQuotientKanMap_isQCatEquivalence_of_positive_stages q
    ((relativeSQuotient_positive_stages_iff_firstRows q).mpr hq)

/-- 概要：同じ有限第一行の比較に条件付きで、元の Verdier 商核四角形が引き戻し。
方針：同じ包含・商辺の核四角形へ元の正段比較を代入する。
規約：有限第一行比較は Sp 正本の未放電の供給入力。
使われ方：同じ未完備 dg 実列の K-6 c5 から K-7 c5・d3 への受け渡し。 -/
theorem quotientSKernelInfinitySquare_isPullback_of_firstRows
    (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (hq : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeFirstRowQuotient q (n + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (quotientSKernelInfinitySquare i q) :=
  quotientSKernelInfinitySquare_isPullback_of_positive_stages i q h
    ((relativeSQuotient_positive_stages_iff_firstRows q).mpr hq)

end SerrePositivity.KST.Fibration
