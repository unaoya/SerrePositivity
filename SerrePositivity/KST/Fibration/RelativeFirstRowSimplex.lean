module
public import SerrePositivity.KST.Fibration.RelativeFirstRowRealization

/-!
概要：元の相対第一行を、同じ商関手の標準単体図式の相対部分複体へ厳密に移す。
方針：K-S• 正本の第一行同型の両向きを、商像が core に入る条件へ制限する。
規約：局所化や分数比較は証明せず、同じ有限図式の座標だけを変える。
使われ方：K-6 c5 の Sp の標準単体図式供給と元の第一行比較の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ)

/-- 概要：同じ商関手で像が core に入る標準単体図式の全相対部分複体。
方針：同じ後合成の下で core の厳密な逆像を取る。
規約：商比較の可逆性は定義に含めない。
使われ方：正段の元の相対第一行を標準単体座標で読む。 -/
def relativeFirstRowSimplex : ((ihom (Δ[n] : SSet.{u})).obj B.obj).Subcomplex :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (Δ[n] : SSet.{u})).obj C.obj)).preimage
    ((ihom (Δ[n] : SSet.{u})).map q.hom)

/-- 概要：元の相対第一行から標準単体座標への実制限写像。
方針：同じ商後合成の自然性と core の関手性で元の同型を制限する。
規約：商射と全図式を保持する。
使われ方：Sp の標準単体供給への順方向の座標変換。 -/
def relativeFirstRowToSimplex : (relativeFirstRow q (n + 1) : SSet.{u}) ⟶
    (relativeFirstRowSimplex q n : SSet.{u}) :=
  Subcomplex.lift ((relativeFirstRow q (n + 1)).ι ≫
    (relativeFirstRowSimplexIso n B.obj).hom) (by
      rintro m _ ⟨x, rfl⟩
      have hx := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (relativeFirstRowSimplexIso n C.obj).hom).app m
        ⟨((ihom (firstRowNerve (n + 1))).map q.hom).app m x.val, x.property⟩).property
      have he := ConcreteCategory.congr_hom
        (NatTrans.congr_app (relativeFirstRowSimplexIso_postcomp q n) m) x.val
      change (relativeFirstRowSimplexIso n C.obj).hom.app m
        (((ihom (firstRowNerve (n + 1))).map q.hom).app m x.val) =
          ((ihom (Δ[n] : SSet.{u})).map q.hom).app m
            ((relativeFirstRowSimplexIso n B.obj).hom.app m x.val) at he
      change ((ihom (Δ[n] : SSet.{u})).map q.hom).app m
        ((relativeFirstRowSimplexIso n B.obj).hom.app m x.val) ∈
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (Δ[n] : SSet.{u})).obj C.obj)).obj m
      rw [← he]
      exact hx)

/-- 概要：標準単体の相対図式から元の相対第一行へ戻す実写像。
方針：同じ座標同型の逆の自然性と core の関手性を使う。
規約：別の第一行代表や商射を選ばない。
使われ方：相対座標変換の両側逆。 -/
def relativeFirstRowFromSimplex : (relativeFirstRowSimplex q n : SSet.{u}) ⟶
    (relativeFirstRow q (n + 1) : SSet.{u}) :=
  Subcomplex.lift ((relativeFirstRowSimplex q n).ι ≫
    (relativeFirstRowSimplexIso n B.obj).inv) (by
      rintro m _ ⟨x, rfl⟩
      have hx := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (relativeFirstRowSimplexIso n C.obj).inv).app m
        ⟨((ihom (Δ[n] : SSet.{u})).map q.hom).app m x.val, x.property⟩).property
      have he := ConcreteCategory.congr_hom (NatTrans.congr_app
        ((internalHom.mapIso (firstRowSimplexIso n).op).inv.naturality q.hom) m) x.val
      change (relativeFirstRowSimplexIso n C.obj).inv.app m
        (((ihom (Δ[n] : SSet.{u})).map q.hom).app m x.val) =
          ((ihom (firstRowNerve (n + 1))).map q.hom).app m
            ((relativeFirstRowSimplexIso n B.obj).inv.app m x.val) at he
      change ((ihom (firstRowNerve (n + 1))).map q.hom).app m
        ((relativeFirstRowSimplexIso n B.obj).inv.app m x.val) ∈
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (firstRowNerve (n + 1))).obj C.obj)).obj m
      rw [← he]
      exact hx)

/-- 概要：相対第一行と同じ商の標準単体相対図式の実同型。
方針：元の座標同型の順逆を同じ相対部分複体へ制限する。
規約：全単体の厳密な両側逆であり、局所化同値では代用しない。
使われ方：標準単体側の商比較を元の相対 S• へ渡す。 -/
def relativeFirstRowSimplexRelativeIso : (relativeFirstRow q (n + 1) : SSet.{u}) ≅
    (relativeFirstRowSimplex q n : SSet.{u}) where
  hom := relativeFirstRowToSimplex q n
  inv := relativeFirstRowFromSimplex q n
  hom_inv_id := by
    apply (cancel_mono (relativeFirstRow q (n + 1)).ι).mp
    change relativeFirstRowToSimplex q n ≫
      ((relativeFirstRowSimplex q n).ι ≫ (relativeFirstRowSimplexIso n B.obj).inv) = _
    rw [← Category.assoc]
    change ((relativeFirstRow q (n + 1)).ι ≫ (relativeFirstRowSimplexIso n B.obj).hom) ≫
      (relativeFirstRowSimplexIso n B.obj).inv = _
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (relativeFirstRowSimplex q n).ι).mp
    change relativeFirstRowFromSimplex q n ≫
      ((relativeFirstRow q (n + 1)).ι ≫ (relativeFirstRowSimplexIso n B.obj).hom) = _
    rw [← Category.assoc]
    change ((relativeFirstRowSimplex q n).ι ≫ (relativeFirstRowSimplexIso n B.obj).inv) ≫
      (relativeFirstRowSimplexIso n B.obj).hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

end SerrePositivity.KST.Fibration
