module
public import SerrePositivity.KST.ProExcision.ColumnRowAffineEquiv
public import SerrePositivity.KST.ProExcision.MonoidBarReversalHomology

/-!
# 非可換な行側半直積と列側半直積の実単体的比較

概要：反対転置の各次数の実半直積同型を全ての面・退化に自然に束ねる。
方針：基底は実 ĜL 自然性、ファイバーは実核イデアル自然性で比較する。
規約：KST Proposition 4.14、SW92 §1.2。係数の単体方向も反転する。
使われ方：行側への相対 bar 零化の実移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open Comparison

/-- 概要：反対係数の列側と反転した行側の反対半直積の実自然同型。
方針：基底とファイバーの実自然性で各次数の実乗法同型を束ねる。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：行側全空間の実比較。 -/
def NonUnitalSimplicialRing.reverseOppositeAffineIso
    (I : NonUnitalSimplicialRing.{u}) (n : ℕ) :
    simplicialActionProduct (I.reverseOpposite.hatGLColumnAction n) ≅
      monoidReverseOpposite (I.rowAffine n) :=
  NatIso.ofComponents (fun k ↦ (I.reverseOppositeAffineMulEquiv n k.unop.len).toMonCatIso)
    (by
      intro k l f
      apply MonCat.hom_ext
      apply MonoidHom.ext
      intro x
      apply MulOpposite.unop_injective
      apply MulOpposite.unop_injective
      apply ActionProduct.ext
      · exact I.reverseOppositeHatGL_natural n f.unop x.base
      · exact integerUnitizationIdealOpVectorMulEquiv_natural (I.obj k)
          (I.map (SimplexCategory.rev.map f.unop).op) n x.fiber)

/-- 概要：反対係数の列側 bar と元の行側 bar の全反転の実同型。
方針：実半直積自然同型の bar と実対角反転同型を合成する。
規約：SW92 §1.2。使われ方：実鎖模型を介した相対零化の移送。 -/
def NonUnitalSimplicialRing.reverseOppositeAffineBarIso
    (I : NonUnitalSimplicialRing.{u}) (n : ℕ) :
    monoidBar (simplicialActionProduct (I.reverseOpposite.hatGLColumnAction n)) ≅
      (monoidBar (I.rowAffine n)).op :=
  monoidBarIso (I.reverseOppositeAffineIso n) ≪≫ monoidBarReverseOppositeIso (I.rowAffine n)

/-- 概要：反対係数の列側と元の行側の実 bar ホモロジー同型。
方針：実空間比較と符号付き鎖反転を借用する H_* の模型に移す。
規約：KST Proposition 4.14、SW92 §1.2。反転不変性の追加仮定は不要。
使われ方：行側相対ホモロジーの全空間の実比較。 -/
def NonUnitalSimplicialRing.reverseOppositeAffineHomologyIso
    (I : NonUnitalSimplicialRing.{u}) (n : ℕ)
    (F : SSet.{u} ⥤ ModuleCat.{u} ℤ) {i : ℕ} (hF : SimplicialHomologyModel F i) :
    F.obj (monoidBar (simplicialActionProduct (I.reverseOpposite.hatGLColumnAction n))) ≅
      F.obj (monoidBar (I.rowAffine n)) :=
  F.mapIso (I.reverseOppositeAffineBarIso n) ≪≫
    hF.reversalNatIso.app (monoidBar (I.rowAffine n))

end SerrePositivity.KST.ProExcision
