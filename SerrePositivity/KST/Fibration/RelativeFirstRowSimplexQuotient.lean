module
public import SerrePositivity.KST.Fibration.RelativeFirstRowSimplex

/-!
概要：同じ相対第一行の商比較を、標準単体図式の元の core 比較へ厳密に移す。
方針：相対座標同型と core の座標同型が作る同じ商可換四角形を使う。
規約：図式局所化・分数比較の証明は Sp 正本に残し、比較射自体を置き換えない。
使われ方：K-6 c5 の標準単体上の具体的な供給命題を元の相対 S• へ代入する。
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
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration
variable {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ)

/-- 概要：同じ商の標準単体相対図式から商図式の core への元の射影。
方針：同じ core 逆像の指定射影を使う。
規約：元の商後合成と全図式を保持する。
使われ方：Sp の有限線型図式供給を受ける実比較射。 -/
def relativeFirstRowSimplexQuotient : (relativeFirstRowSimplex q n : SSet.{u}) ⟶
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (Δ[n] : SSet.{u})).obj C.obj) : SSet.{u}) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (Δ[n] : SSet.{u})).obj C.obj)).fromPreimage
    ((ihom (Δ[n] : SSet.{u})).map q.hom)

/-- 概要：標準単体商比較の包含後は、同じ元の商関手による後合成。
方針：core 逆像の指定射影を展開する。
規約：全単体写像の厳密等式。
使われ方：元の第一行商比較との照合。 -/
theorem relativeFirstRowSimplexQuotient_ι :
    relativeFirstRowSimplexQuotient q n ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (Δ[n] : SSet.{u})).obj C.obj)).ι =
      (relativeFirstRowSimplex q n).ι ≫ (ihom (Δ[n] : SSet.{u})).map q.hom := rfl

/-- 概要：元の相対第一行の商比較は標準単体の同じ商比較と厳密に可換。
方針：元の core 包含で消去し、同じ座標変換の後合成自然性を使う。
規約：四つの元の全単体写像を保持する。
使われ方：標準単体側の供給を第一行側の同じ比較へ戻す。 -/
theorem relativeFirstRowSimplexQuotient_square :
    relativeFirstRowToSimplex q n ≫ relativeFirstRowSimplexQuotient q n =
      relativeFirstRowQuotient q (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (relativeFirstRowSimplexIso n C.obj).hom := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (Δ[n] : SSet.{u})).obj C.obj)).ι).mp
  rw [Category.assoc, relativeFirstRowSimplexQuotient_ι, ← Category.assoc]
  change ((relativeFirstRow q (n + 1)).ι ≫ (relativeFirstRowSimplexIso n B.obj).hom) ≫
    (ihom (Δ[n] : SSet.{u})).map q.hom = _
  rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι,
    ← Category.assoc (relativeFirstRowQuotient q (n + 1)), relativeFirstRowQuotient_ι,
    Category.assoc, relativeFirstRowSimplexIso_postcomp]

/-- 概要：同じ第一行商比較の可逆性は標準単体商比較の可逆性と同値。
方針：同じ厳密四角形の両座標同型を元の anodyne 局所化へ写す。
規約：標準単体商比較の可逆性自体は未放電の Sp 供給に残す。
使われ方：元の正段入力と Sp の有限標準単体比較を同一の条件として照合する。 -/
theorem relativeFirstRowQuotient_localized_isIso_iff_simplex :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeFirstRowQuotient q (n + 1))) ↔
      IsIso (AnodyneHomotopy.anodyneQ.map (relativeFirstRowSimplexQuotient q n)) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have hs : IsIso (Q.map (relativeFirstRowToSimplex q n)) := by
    change IsIso (Q.map (relativeFirstRowSimplexRelativeIso q n).hom)
    infer_instance
  have ht : IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (relativeFirstRowSimplexIso n C.obj).hom)) := by
    change IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (relativeFirstRowSimplexIso n C.obj).hom))
    infer_instance
  have he := congrArg Q.map (relativeFirstRowSimplexQuotient_square q n)
  rw [Q.map_comp, Q.map_comp] at he
  constructor
  · intro h
    have hm : IsIso (Q.map (relativeFirstRowToSimplex q n) ≫
        Q.map (relativeFirstRowSimplexQuotient q n)) := by
      rw [he]
      infer_instance
    exact (isIso_comp_left_iff _ _).mp hm
  · intro h
    have hm : IsIso (Q.map (relativeFirstRowQuotient q (n + 1)) ≫
        Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (relativeFirstRowSimplexIso n C.obj).hom)) := by
      rw [← he]
      infer_instance
    exact (isIso_comp_right_iff _ _).mp hm

/-- 概要：元の相対 S• 正段比較は同じ商の標準単体図式比較と同値。
方針：元の第一行四角形と標準単体四角形の二つの厳密比較を続ける。
規約：新たな局所化存在入力や core 比較の無条件性は主張しない。
使われ方：K-6 c5 の元の hstage 引数への標準単体供給の代入。 -/
theorem relativeSQuotient_localized_isIso_iff_firstRowSimplex :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeSQuotientMap q (n + 1))) ↔
      IsIso (AnodyneHomotopy.anodyneQ.map (relativeFirstRowSimplexQuotient q n)) :=
  (relativeSQuotient_localized_isIso_iff_firstRow q (n + 1)).trans
    (relativeFirstRowQuotient_localized_isIso_iff_simplex q n)

/-- 概要：同じ標準単体図式の比較に条件付きで、元の相対 S• 商実現が可逆。
方針：各標準単体比較を同じ元の第一行比較に戻して対角実現へ渡す。
規約：Sp 正本の有限図式比較の存在や無条件の連結版は主張しない。
使われ方：K-6 c5 の標準単体供給を元の実現射へ直接代入する。 -/
theorem relativeSQuotientRealization_localized_isIso_of_firstRowSimplices
    (hq : ∀ m : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
      (relativeFirstRowSimplexQuotient q m))) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (simplicialDiagonalFunctor.map (relativeSimplicialQuotientMap q))) :=
  relativeSQuotientRealization_localized_isIso_of_firstRows q
    (fun m => (relativeFirstRowQuotient_localized_isIso_iff_simplex q m).mpr (hq m))

end SerrePositivity.KST.Fibration
